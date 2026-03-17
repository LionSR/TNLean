/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.MPVOverlapDecay
import TNLean.QPF.Assembly
import TNLean.Channel.FixedPoint.CanonicalGauge
import TNLean.Channel.Schwarz.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Rectangular spectral gap for the mixed transfer operator

When two MPS tensors `A : MPSTensor d D₁` and `B : MPSTensor d D₂` have **different bond
dimensions** `D₁ ≠ D₂`, the spectral radius of the rectangular mixed transfer operator
`mixedTransferMap₂ A B` is strictly less than 1 (assuming both tensors are injective and
normalized).

This is the "dimension-mismatch" spectral gap: if the bond dimensions differ, then the overlap
`∑ σ, mpv A σ * conj(mpv B σ)` decays to zero exponentially.

## Main results

* `mixedTransferSpectralRadius₂_lt_one_of_dim_ne`: strict spectral gap for dimension-mismatched
  normalized injective tensors
* `mpvOverlap_tendsto_zero_of_dim_ne`: the MPV overlap tends to zero when `D₁ ≠ D₂`

## Proof outline

1. **Eigenvalue bound ≤ 1**: Frobenius-norm contraction adapted to the rectangular setting.
2. **Equality case implies D₁ = D₂**: Block-embed into `Fin D₁ ⊕ Fin D₂`, apply
   Kadison–Schwarz equality to extract Kraus-level intertwining, then show `ker X = 0`
   and `ker X† = 0` using injectivity of the generators, which forces `D₁ = D₂`.
3. Contraposition gives `D₁ ≠ D₂ ⟹ spectralRadius < 1`.

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007, Lemma 5.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators NNReal ENNReal Matrix.Norms.Elementwise

namespace MPSTensor

variable {d D₁ D₂ : ℕ}

/-! ## Rectangular spectral radius abbreviation -/

/-- The **spectral radius** of the rectangular mixed transfer operator. -/
noncomputable def mixedTransferSpectralRadius₂
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
      (mixedTransferMap₂ A B))

theorem mixedTransferSpectralRadius₂_eq
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) :
    mixedTransferSpectralRadius₂ A B =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
          (mixedTransferMap₂ A B)) := rfl

/-! ## Rectangular Frobenius norm -/

section FrobeniusRect

/-- Frobenius norm squared of a rectangular matrix: `∑ i j, ‖X i j‖²`. -/
noncomputable def frobSq₂ (X : Matrix (Fin D₁) (Fin D₂) ℂ) : ℝ :=
  ∑ i : Fin D₁, ∑ j : Fin D₂, ‖X i j‖ ^ 2

lemma frobSq₂_nonneg (X : Matrix (Fin D₁) (Fin D₂) ℂ) : 0 ≤ frobSq₂ X :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

lemma frobSq₂_eq_zero_iff (X : Matrix (Fin D₁) (Fin D₂) ℂ) : frobSq₂ X = 0 ↔ X = 0 := by
  constructor
  · intro h; ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => by positivity).mp h i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).mp h1 j
      (Finset.mem_univ _)
    rwa [sq_eq_zero_iff, norm_eq_zero] at h2
  · rintro rfl; simp [frobSq₂]

lemma frobSq₂_pos_of_ne_zero (X : Matrix (Fin D₁) (Fin D₂) ℂ) (hX : X ≠ 0) :
    0 < frobSq₂ X :=
  lt_of_le_of_ne (frobSq₂_nonneg X) (Ne.symm (mt (frobSq₂_eq_zero_iff X).mp hX))

lemma frobSq₂_smul (c : ℂ) (X : Matrix (Fin D₁) (Fin D₂) ℂ) :
    frobSq₂ (c • X) = ‖c‖ ^ 2 * frobSq₂ X := by
  simp only [frobSq₂, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

private lemma frobSq₂_trace (X : Matrix (Fin D₁) (Fin D₂) ℂ) :
    frobSq₂ X = (Matrix.trace (Xᴴ * X)).re := by
  simp only [frobSq₂, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext j
  rw [show star (X j i) * X j i = ↑(Complex.normSq (X j i)) from
    Complex.normSq_eq_conj_mul_self.symm, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end FrobeniusRect

/-! ## Euclidean space embedding for rectangular matrices -/

section HSRect

private noncomputable def toES₂ (M : Matrix (Fin D₁) (Fin D₂) ℂ) :
    EuclideanSpace ℂ (Fin D₁ × Fin D₂) :=
  (EuclideanSpace.equiv (Fin D₁ × Fin D₂) ℂ).symm (fun p => M p.1 p.2)

@[simp] private lemma toES₂_apply (M : Matrix (Fin D₁) (Fin D₂) ℂ) (p : Fin D₁ × Fin D₂) :
    toES₂ M p = M p.1 p.2 := by simp [toES₂, EuclideanSpace.equiv]

private lemma toES₂_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin D₁) (Fin D₂) ℂ) :
    toES₂ (∑ i ∈ s, f i) = ∑ i ∈ s, toES₂ (f i) := by
  ext p; simp [Matrix.sum_apply, Finset.sum_apply]

private lemma norm_toES₂_sq (M : Matrix (Fin D₁) (Fin D₂) ℂ) :
    ‖toES₂ M‖ ^ 2 = frobSq₂ M := by
  rw [sq, ← @inner_self_eq_norm_mul_norm ℂ]
  change RCLike.re (@inner ℂ _ _ (toES₂ M) (toES₂ M)) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply', toES₂_apply, starRingEnd_apply]
  rw [show (∑ x : Fin D₁ × Fin D₂, star (M x.1 x.2) * M x.1 x.2) =
    ∑ i, ∑ j, star (M i j) * M i j from Fintype.sum_prod_type _]
  simp only [frobSq₂, Complex.re_sum, RCLike.re_to_complex]
  congr 1; ext i; congr 1; ext j
  rw [mul_comm, show M i j * star (M i j) = (↑(‖M i j‖ ^ 2) : ℂ) from by
    rw [show star (M i j) = starRingEnd ℂ (M i j) from rfl, Complex.mul_conj',
      ← Complex.ofReal_pow]]
  exact Complex.ofReal_re _

/-- Euclidean space embedding for square D₁×D₁ matrices (local copy for cross-shape bounds). -/
private noncomputable def toESSq₁ (M : Matrix (Fin D₁) (Fin D₁) ℂ) :
    EuclideanSpace ℂ (Fin D₁ × Fin D₁) :=
  (EuclideanSpace.equiv (Fin D₁ × Fin D₁) ℂ).symm (fun p => M p.1 p.2)

@[simp] private lemma toESSq₁_apply (M : Matrix (Fin D₁) (Fin D₁) ℂ) (p : Fin D₁ × Fin D₁) :
    toESSq₁ M p = M p.1 p.2 := by simp [toESSq₁, EuclideanSpace.equiv]

private lemma norm_toESSq₁_sq (M : Matrix (Fin D₁) (Fin D₁) ℂ) :
    ‖toESSq₁ M‖ ^ 2 = frobSq₂ M := by
  rw [sq, ← @inner_self_eq_norm_mul_norm ℂ]
  change RCLike.re (@inner ℂ _ _ (toESSq₁ M) (toESSq₁ M)) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply', toESSq₁_apply, starRingEnd_apply]
  rw [show (∑ x : Fin D₁ × Fin D₁, star (M x.1 x.2) * M x.1 x.2) =
    ∑ i, ∑ j, star (M i j) * M i j from Fintype.sum_prod_type _]
  simp only [frobSq₂, Complex.re_sum, RCLike.re_to_complex]
  congr 1; ext i; congr 1; ext j
  rw [mul_comm, show M i j * star (M i j) = (↑(‖M i j‖ ^ 2) : ℂ) from by
    rw [show star (M i j) = starRingEnd ℂ (M i j) from rfl, Complex.mul_conj',
      ← Complex.ofReal_pow]]
  exact Complex.ofReal_re _

private lemma toESSq₁_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin D₁) (Fin D₁) ℂ) :
    toESSq₁ (∑ i ∈ s, f i) = ∑ i ∈ s, toESSq₁ (f i) := by
  ext p; simp [Matrix.sum_apply, Finset.sum_apply]

private lemma norm_toES₂_mul_le
    (A : Matrix (Fin D₁) (Fin D₁) ℂ) (B : Matrix (Fin D₁) (Fin D₂) ℂ) :
    ‖toES₂ (A * B)‖ ≤ ‖toESSq₁ A‖ * ‖toES₂ B‖ := by
  have h : ‖toES₂ (A * B)‖ ^ 2 ≤ (‖toESSq₁ A‖ * ‖toES₂ B‖) ^ 2 := by
    rw [norm_toES₂_sq, mul_pow, norm_toESSq₁_sq, norm_toES₂_sq]
    -- Frobenius submultiplicativity for mixed-shape matrices
    simp only [frobSq₂, Matrix.mul_apply]
    have norm_sq_cs (a b : Fin D₁ → ℂ) :
        ‖∑ k, a k * b k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) :=
      (pow_le_pow_left₀ (norm_nonneg _)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_mul_le _ _)) 2).trans
        (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
        ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            norm_sq_cs _ _
      _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
          (congr 1; exact Finset.sum_comm)
  nlinarith [Real.sqrt_le_sqrt h, Real.sqrt_sq (norm_nonneg (toES₂ (A * B))),
    Real.sqrt_sq (mul_nonneg (norm_nonneg (toESSq₁ A)) (norm_nonneg (toES₂ B)))]

end HSRect

/-! ## Hilbert–Schmidt contraction for the rectangular mixed transfer -/

section HSContraction

/-- Right-sum identity: `∑_σ ‖X · w_B(σ)†‖_F² = ‖X‖_F²` for rectangular X.

The proof uses trace cycling: `frobSq₂(v M†) = tr(M† M · v† v).re`, then sum over σ. -/
private lemma sum_frobSq₂_right (B : MPSTensor d D₂) (hB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (v : Matrix (Fin D₁) (Fin D₂) ℂ) (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq₂ (v * (evalWord B (List.ofFn σ))ᴴ) = frobSq₂ v := by
  -- Trace-cycle: tr((v M†)† (v M†)) = tr(M† M v† v)
  have trace_cycle : ∀ M : Matrix (Fin D₂) (Fin D₂) ℂ,
      ((v * Mᴴ)ᴴ * (v * Mᴴ)).trace = (Mᴴ * M * (vᴴ * v)).trace := by
    intro M
    have h1 : (v * Mᴴ)ᴴ = M * vᴴ := by
      simp [Matrix.conjTranspose_mul]
    rw [h1]
    rw [Matrix.mul_assoc M vᴴ _, ← Matrix.mul_assoc vᴴ v Mᴴ,
      ← Matrix.mul_assoc M (vᴴ * v) Mᴴ,
      Matrix.trace_mul_comm (M * (vᴴ * v)) Mᴴ,
      ← Matrix.mul_assoc Mᴴ M (vᴴ * v)]
  -- Apply trace cycling to the sum.
  simp_rw [frobSq₂_trace]
  conv_lhs => arg 2; ext σ; rw [trace_cycle (evalWord B (List.ofFn σ))]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
    word_conjTranspose_mul_sum B hB n, Matrix.one_mul]

/-- Word Frobenius norm sum for square matrices: `∑_σ ‖w_K(σ)‖_F² = D₁`. -/
private lemma sum_frobSq₂_words (K : MPSTensor d D₁) (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1)
    (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq₂ (evalWord K (List.ofFn σ)) = (D₁ : ℝ) := by
  simp_rw [frobSq₂_trace]
  rw [← Complex.re_sum, ← Matrix.trace_sum, word_conjTranspose_mul_sum K hK n]
  simp [Matrix.trace_one, Fintype.card_fin]

/-- **Uniform Frobenius-norm bound**: `‖F₂^n(X)‖_F² ≤ D₁² · ‖X‖_F²` for the rectangular
mixed transfer operator. -/
private lemma hs_contraction_rect [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂) (X : Matrix (Fin D₁) (Fin D₂) ℂ)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) (n : ℕ) :
    frobSq₂ (((mixedTransferMap₂ A B) ^ n) X) ≤ (D₁ : ℝ) ^ 2 * frobSq₂ X := by
  rw [mixedTransferMap₂_pow_apply, show (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ) =
    (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) from by
    congr 1; ext σ; rw [Matrix.mul_assoc]]
  rw [show frobSq₂ (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) =
    ‖toES₂ (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ^ 2 from
    (norm_toES₂_sq _).symm]
  set fA := fun σ : Fin n → Fin d => ‖toESSq₁ (evalWord A (List.ofFn σ))‖ with hfA_def
  set fB := fun σ : Fin n → Fin d => ‖toES₂ (X * (evalWord B (List.ofFn σ))ᴴ)‖ with hfB_def
  have h_chain : ‖toES₂ (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ≤
    ∑ σ : Fin n → Fin d, fA σ * fB σ :=
    ((by rw [toES₂_finset_sum]; exact norm_sum_le _ _) : ‖toES₂ _‖ ≤ _).trans
      (Finset.sum_le_sum fun σ _ => norm_toES₂_mul_le _ _)
  have h_A : ∑ σ : Fin n → Fin d, fA σ ^ 2 = (D₁ : ℝ) := by
    simp_rw [hfA_def, norm_toESSq₁_sq]; exact sum_frobSq₂_words A hA_norm n
  have h_B : ∑ σ : Fin n → Fin d, fB σ ^ 2 = frobSq₂ X := by
    simp_rw [hfB_def, norm_toES₂_sq]; exact sum_frobSq₂_right B hB_norm X n
  calc ‖toES₂ _‖ ^ 2
      ≤ (∑ σ : Fin n → Fin d, fA σ * fB σ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_chain 2
    _ ≤ (∑ σ, fA σ ^ 2) * (∑ σ, fB σ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ fA fB
    _ = (D₁ : ℝ) * frobSq₂ X := by rw [h_A, h_B]
    _ ≤ (D₁ : ℝ) ^ 2 * frobSq₂ X := by
        nlinarith [sq_nonneg ((D₁ : ℝ) - 1), frobSq₂_nonneg X,
          show (1 : ℝ) ≤ D₁ from by exact_mod_cast NeZero.one_le (n := D₁)]

end HSContraction

/-! ## Eigenvalue bound -/

section EigenvalueBound

/-- Every eigenvalue of the rectangular mixed transfer operator has modulus ≤ 1. -/
theorem eigenvalue_norm_le_one₂ [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedTransferMap₂ A B) μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ.exists_hasEigenvector
  have hFv := Module.End.mem_eigenspace_iff.mp hv_mem
  by_contra h_gt; push_neg at h_gt
  have h_pos := frobSq₂_pos_of_ne_zero v hv_ne
  have h_bound : ∀ n : ℕ, ‖μ‖ ^ (2 * n) ≤ (D₁ : ℝ) ^ 2 := fun n => by
    have h1 := hs_contraction_rect A B v hA_norm hB_norm n
    rw [eigenvector_pow _ v μ hFv n, frobSq₂_smul, norm_pow] at h1
    calc ‖μ‖ ^ (2 * n) = (‖μ‖ ^ n) ^ 2 := by ring
    _ ≤ _ := le_of_mul_le_mul_right (by linarith) h_pos
  have htend := tendsto_pow_atTop_atTop_of_one_lt (by nlinarith : 1 < ‖μ‖ ^ 2)
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨n, hn⟩ := htend ((D₁ : ℝ) ^ 2 + 1)
  linarith [h_bound n, show (‖μ‖ ^ 2) ^ n = ‖μ‖ ^ (2 * n) from by ring, hn n le_rfl]

/-- **Spectral radius bound**: `ρ(F₂) ≤ 1` for normalized tensors. -/
theorem spectralRadius_mixedTransfer₂_le_one
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    mixedTransferSpectralRadius₂ A B ≤ 1 := by
  rw [mixedTransferSpectralRadius₂_eq]
  rcases eq_or_ne D₁ 0 with rfl | hD₁
  · have : Subsingleton (Matrix (Fin 0) (Fin D₂) ℂ) := ⟨fun a b => by ext i; exact i.elim0⟩
    have : Subsingleton (Matrix (Fin 0) (Fin D₂) ℂ →L[ℂ] Matrix (Fin 0) (Fin D₂) ℂ) :=
      ContinuousLinearMap.uniqueOfLeft.instSubsingleton
    rw [spectrum.SpectralRadius.of_subsingleton]; exact zero_le _
  · rcases eq_or_ne D₂ 0 with rfl | hD₂
    · have : Subsingleton (Matrix (Fin D₁) (Fin 0) ℂ) := ⟨fun a b => by ext i j; exact j.elim0⟩
      have : Subsingleton (Matrix (Fin D₁) (Fin 0) ℂ →L[ℂ] Matrix (Fin D₁) (Fin 0) ℂ) :=
        ContinuousLinearMap.uniqueOfLeft.instSubsingleton
      rw [spectrum.SpectralRadius.of_subsingleton]; exact zero_le _
    · haveI : NeZero D₁ := ⟨hD₁⟩
      haveI : NeZero D₂ := ⟨hD₂⟩
      have h_spec := AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap
        (Matrix (Fin D₁) (Fin D₂) ℂ)) (mixedTransferMap₂ A B)
      apply iSup₂_le; intro k hk
      rw [ENNReal.coe_le_one_iff]
      exact_mod_cast eigenvalue_norm_le_one₂ A B hA_norm hB_norm k
        (Module.End.hasEigenvalue_iff_mem_spectrum.mpr (h_spec ▸ hk))

end EigenvalueBound

/-! ## Modulus-1 eigenvalue implies equal dimensions -/

section DimensionEquality

/-- If `X ≠ 0` and `ker(X)` is invariant under all `D₂ × D₂` matrices,
then `X` has trivial kernel (is injective as a linear map). -/
private lemma injective_of_ker_all [NeZero D₂]
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) (hX : X ≠ 0)
    (h_all : ∀ M : Matrix (Fin D₂) (Fin D₂) ℂ, ∀ v, X *ᵥ v = 0 → X *ᵥ (M *ᵥ v) = 0) :
    ∀ v : Fin D₂ → ℂ, X *ᵥ v = 0 → v = 0 := by
  intro v hv
  by_contra hv_ne
  -- v ≠ 0, Xv = 0; show Xw = 0 for all w, hence X = 0
  have ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h_all_zero; push_neg at h_all_zero
    exact hv_ne (funext h_all_zero)
  have h_surj : ∀ w : Fin D₂ → ℂ, X *ᵥ w = 0 := by
    intro w
    let c : Fin D₂ → ℂ := fun j => if j = k then (v k)⁻¹ else 0
    have hMv : (Matrix.vecMulVec w c) *ᵥ v = w := by
      ext i
      simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, dotProduct]
      conv_lhs => arg 2; ext j; rw [mul_assoc]
      rw [Finset.sum_eq_single k]
      · simp [c, hk]
      · intro j _ hjk; simp [c, hjk]
      · intro hk_abs; exact absurd (Finset.mem_univ k) hk_abs
    rw [← hMv]; exact h_all _ v hv
  have h_X_zero : X = 0 := by
    ext i j
    have h_ej := h_surj (fun k => if k = j then 1 else 0)
    have : (X *ᵥ (fun k => if k = j then 1 else 0)) i = X i j := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj; simp [hbj]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [show (0 : Matrix (Fin D₁) (Fin D₂) ℂ) i j = 0 from rfl]
    rw [← this]; exact congr_fun h_ej i
  exact hX h_X_zero

/-- Conjugation by an invertible matrix preserves injectivity (spanning). -/
private lemma isInjective_conjugate {D : ℕ}
    (T : MPSTensor d D) (hT : IsInjective T)
    (S : Matrix (Fin D) (Fin D) ℂ) (hS : S.det ≠ 0) :
    IsInjective (fun i => S⁻¹ * T i * S) := by
  let φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    (LinearMap.mulLeft ℂ S⁻¹).comp (LinearMap.mulRight ℂ S)
  have hφ_surj : Function.Surjective φ := by
    intro N
    refine ⟨S * N * S⁻¹, ?_⟩
    simp only [φ, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ (Ne.isUnit hS), mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hS)]
  have : Submodule.span ℂ (Set.range (fun i => S⁻¹ * T i * S)) = ⊤ := by
    have himage : (⇑φ '' Set.range T) = Set.range (fun i => S⁻¹ * T i * S) := by
      ext Y; constructor
      · rintro ⟨X0, ⟨i, rfl⟩, rfl⟩; exact ⟨i, by simp [φ, Matrix.mul_assoc]⟩
      · rintro ⟨i, rfl⟩; refine ⟨T i, ⟨i, rfl⟩, by simp [φ, Matrix.mul_assoc]⟩
    calc Submodule.span ℂ (Set.range (fun i => S⁻¹ * T i * S))
        = Submodule.map φ (Submodule.span ℂ (Set.range T)) := by
          simpa [himage] using (Submodule.map_span (f := φ) (s := Set.range T)).symm
      _ = Submodule.map φ ⊤ := by rw [hT]
      _ = ⊤ := by rw [Submodule.map_top]; exact LinearMap.range_eq_top.2 hφ_surj
  exact this

/-- Core algebraic lemma: if there is an eigenvector of `mixedTransferMap₂ A B` with eigenvalue
of modulus 1, then `D₁ = D₂`.

This is the rectangular analogue of `eigenvector_gives_gauge` from `SpectralGap.lean`,
but instead of constructing a gauge equivalence, we derive equality of dimensions. -/
private theorem dim_eq_of_modulus_one_eigenvector [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (X : Matrix (Fin D₁) (Fin D₂) ℂ) (μ : ℂ)
    (hFX : mixedTransferMap₂ A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    D₁ = D₂ := by
  classical
  -- === 1. QPF fixed points ===
  obtain ⟨ρA, hρA⟩ := injective_transfer_unique_fixed_point' A hA hA_norm
  obtain ⟨ρB, hρB⟩ := injective_transfer_unique_fixed_point' B hB hB_norm
  -- === 2. Cholesky factorization ===
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).1
      (hρA.pos_def.isStrictlyPositive) with ⟨S0A, hS0A_unit, hρA_eq'⟩
  have hρA_eq : ρA = S0Aᴴ * S0A := by
    simpa [Matrix.star_eq_conjTranspose] using hρA_eq'
  rcases (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).1
      (hρB.pos_def.isStrictlyPositive) with ⟨S0B, hS0B_unit, hρB_eq'⟩
  have hρB_eq : ρB = S0Bᴴ * S0B := by
    simpa [Matrix.star_eq_conjTranspose] using hρB_eq'
  let SA : Matrix (Fin D₁) (Fin D₁) ℂ := S0Aᴴ
  let SB : Matrix (Fin D₂) (Fin D₂) ℂ := S0Bᴴ
  -- Determinant facts
  have hSA_det : SA.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A := SA)).1
      (by simpa [SA, Matrix.star_eq_conjTranspose] using IsUnit.star hS0A_unit)).ne_zero
  have hSB_det : SB.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (A := SB)).1
      (by simpa [SB, Matrix.star_eq_conjTranspose] using IsUnit.star hS0B_unit)).ne_zero
  have hSA_u := Ne.isUnit hSA_det
  have hSB_u := Ne.isUnit hSB_det
  have hSAh_det : (SAᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSA_det
  have hSBh_det : (SBᴴ).det ≠ 0 := by
    simpa [Matrix.det_conjTranspose] using star_ne_zero.mpr hSB_det
  have hSAh_u := Ne.isUnit hSAh_det
  have hSBh_u := Ne.isUnit hSBh_det
  -- Cancellation lemmas
  have hSA_mul : SA * SAᴴ = ρA := by
    calc SA * SAᴴ = S0Aᴴ * S0A := by simp [SA]
    _ = ρA := by simpa using hρA_eq.symm
  have hSB_mul : SB * SBᴴ = ρB := by
    calc SB * SBᴴ = S0Bᴴ * S0B := by simp [SB]
    _ = ρB := by simpa using hρB_eq.symm
  -- === 3. Left-canonical-gauged tensors ===
  let A' : MPSTensor d D₁ := fun i => SA⁻¹ * A i * SA
  let B' : MPSTensor d D₂ := fun i => SB⁻¹ * B i * SB
  have hA'unital : ∑ i : Fin d, (A' i) * (A' i)ᴴ = 1 := by
    simpa [A'] using gauged_unital A SA ρA hSA_det hSA_mul hρA.fixed
  have hB'unital : ∑ i : Fin d, (B' i) * (B' i)ᴴ = 1 := by
    simpa [B'] using gauged_unital B SB ρB hSB_det hSB_mul hρB.fixed
  -- === 4. Gauged eigenvector ===
  let X' : Matrix (Fin D₁) (Fin D₂) ℂ := SA⁻¹ * X * (SBᴴ)⁻¹
  have hX'ne : X' ≠ 0 := by
    intro h0; apply hX
    have key : SA * X' * SBᴴ = X := by
      simp only [X', Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u,
          Matrix.nonsing_inv_mul _ hSBh_u, Matrix.mul_one]
    rw [← key, h0, Matrix.mul_zero, Matrix.zero_mul]
  -- Gauged eigenvector equation
  have hFXsum : ∑ i : Fin d, A i * X * (B i)ᴴ = μ • X := by
    simpa [mixedTransferMap₂_apply] using hFX
  have hFX' : ∑ i : Fin d, A' i * X' * (B' i)ᴴ = μ • X' := by
    have hterm : ∀ i : Fin d,
        (A' i) * X' * (B' i)ᴴ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
      intro i
      have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
        simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
      calc (A' i) * X' * (B' i)ᴴ
          = (SA⁻¹ * A i * SA) * (SA⁻¹ * X * (SBᴴ)⁻¹) * (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) := by
            simp [A', X', hBstar]
        _ = SA⁻¹ * (A i * X * (B i)ᴴ) * (SBᴴ)⁻¹ := by
            simp only [Matrix.mul_assoc]
            rw [Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u,
                Matrix.nonsing_inv_mul_cancel_left _ _ hSBh_u]
    -- Factor out the constant matrices on the left/right of the sum.
    -- First rewrite each term using `hterm`, then factor out the constant matrices on the
    -- right and left of the sum.
    simp_rw [hterm]
    -- factor out right multiplication by `(SBᴴ)⁻¹`
    simp_rw [← Matrix.sum_mul (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => SA⁻¹ * (A i * X * (B i)ᴴ)) (M := (SBᴴ)⁻¹)]
    -- factor out left multiplication by `SA⁻¹`
    simp_rw [← Matrix.mul_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => A i * X * (B i)ᴴ) (M := SA⁻¹)]
    -- Now use the original eigenvector equation `hFXsum`.
    -- (After factoring) the goal is
    --   `(SA⁻¹ * (∑ i, A i * X * (B i)ᴴ)) * (SBᴴ)⁻¹ = μ • X'`.
    rw [hFXsum]
    -- Move the scalar `μ` out of the two matrix multiplications.
    have h1 : SA⁻¹ * (μ • X) = μ • (SA⁻¹ * X) := by
      simp [Matrix.mul_smul]
    rw [h1]
    have h2 : (μ • (SA⁻¹ * X)) * (SBᴴ)⁻¹ = μ • ((SA⁻¹ * X) * (SBᴴ)⁻¹) := by
      simp [Matrix.smul_mul]
    rw [h2]
  -- === 5. Block embedding ===
  let K : Fin d → Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    fun i => Matrix.fromBlocks (A' i) 0 0 (B' i)
  let M : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    Matrix.fromBlocks 0 X' 0 0
  have hK_unital : Kraus.IsUnital K := by
    change (∑ i, K i * (K i)ᴴ) = 1
    have hsum : ∑ i : Fin d, K i * (K i)ᴴ =
        Matrix.fromBlocks (∑ i, (A' i) * (A' i)ᴴ) 0 0 (∑ i, (B' i) * (B' i)ᴴ) := by
      ext a b; rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [K, Matrix.sum_apply, Matrix.fromBlocks_multiply,
              Matrix.fromBlocks_conjTranspose]
    simp [hsum, hA'unital, hB'unital]
  have hEigM : Kraus.map K M = μ • M := by
    have hmap : Kraus.map K M =
        Matrix.fromBlocks 0 (∑ i : Fin d, A' i * X' * (B' i)ᴴ) 0 0 := by
      ext a b; rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [Kraus.map, K, M, Matrix.sum_apply, Matrix.fromBlocks_multiply,
              Matrix.fromBlocks_conjTranspose]
    simp [hmap, hFX', M, Matrix.fromBlocks_smul]
  -- PD fixed point for adjoint Kraus map
  let rhoT : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
    Matrix.fromBlocks (SAᴴ * SA) 0 0 (SBᴴ * SB)
  have hrhoT_pd : rhoT.PosDef := by
    let Sblock : Matrix (Fin D₁ ⊕ Fin D₂) (Fin D₁ ⊕ Fin D₂) ℂ :=
      Matrix.fromBlocks SA 0 0 SB
    refine (Matrix.isStrictlyPositive_iff_posDef).1 ?_
    refine (CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self).2 ?_
    refine ⟨Sblock, ?_, ?_⟩
    · exact (isUnit_iff_exists_inv).2
        ⟨Matrix.fromBlocks SA⁻¹ 0 0 SB⁻¹, by
          simp [Sblock, Matrix.fromBlocks_multiply,
                Matrix.mul_nonsing_inv _ hSA_u, Matrix.mul_nonsing_inv _ hSB_u]⟩
    · simp [rhoT, Sblock, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
        Matrix.fromBlocks_multiply]
  have hrhoT_fix : Kraus.adjointMap K rhoT = rhoT := by
    -- Each diagonal block: ∑ (A'_i)† (SA† SA) A'_i = SA† SA (similarly for B)
    have hAblock : ∑ i : Fin d, (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * SA := by
      have hterm : ∀ i : Fin d,
          (A' i)ᴴ * (SAᴴ * SA) * (A' i) = SAᴴ * ((A i)ᴴ * A i) * SA := by
        intro i
        have hAstar : (A' i)ᴴ = SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹ := by
          simp [A', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
        calc (A' i)ᴴ * (SAᴴ * SA) * (A' i)
            = (SAᴴ * (A i)ᴴ * (SAᴴ)⁻¹) * (SAᴴ * SA) * (SA⁻¹ * A i * SA) := by
              simp [A', hAstar]
          _ = SAᴴ * ((A i)ᴴ * A i) * SA := by
              simp only [Matrix.mul_assoc]
              rw [Matrix.nonsing_inv_mul_cancel_left _ _ hSAh_u,
                  Matrix.mul_nonsing_inv_cancel_left _ _ hSA_u]
      simp_rw [hterm, ← Finset.sum_mul, ← Finset.mul_sum, hA_norm, Matrix.mul_one]
    have hBblock : ∑ i : Fin d, (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * SB := by
      have hterm : ∀ i : Fin d,
          (B' i)ᴴ * (SBᴴ * SB) * (B' i) = SBᴴ * ((B i)ᴴ * B i) * SB := by
        intro i
        have hBstar : (B' i)ᴴ = SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹ := by
          simp [B', Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
        calc (B' i)ᴴ * (SBᴴ * SB) * (B' i)
            = (SBᴴ * (B i)ᴴ * (SBᴴ)⁻¹) * (SBᴴ * SB) * (SB⁻¹ * B i * SB) := by
              simp [B', hBstar]
          _ = SBᴴ * ((B i)ᴴ * B i) * SB := by
              simp only [Matrix.mul_assoc]
              rw [Matrix.nonsing_inv_mul_cancel_left _ _ hSBh_u,
                  Matrix.mul_nonsing_inv_cancel_left _ _ hSB_u]
      simp_rw [hterm, ← Finset.sum_mul, ← Finset.mul_sum, hB_norm, Matrix.mul_one]
    have hAdj : Kraus.adjointMap K rhoT =
        Matrix.fromBlocks (∑ i, (A' i)ᴴ * (SAᴴ * SA) * (A' i)) 0 0
          (∑ i, (B' i)ᴴ * (SBᴴ * SB) * (B' i)) := by
      ext a b; rcases a with (a | a) <;> rcases b with (b | b) <;>
        simp [Kraus.adjointMap, K, rhoT, Matrix.sum_apply, Matrix.fromBlocks_multiply,
              Matrix.fromBlocks_conjTranspose]
    simp [hAdj, rhoT, hAblock, hBblock]
  -- === 6. KS equality + commutation ===
  have hKS_M : Kraus.map K (Mᴴ * M) = (Kraus.map K M)ᴴ * Kraus.map K M :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hK_unital hrhoT_pd hrhoT_fix M μ hEigM hμ
  have hComm_M : ∀ i : Fin d, M * (K i)ᴴ = (K i)ᴴ * Kraus.map K M :=
    Kraus.kraus_commute_of_ks_equality K hK_unital M hKS_M
  -- === 7. Intertwining: X' * (B' k)† = μ • (A' k)† * X' ===
  have hInter1 : ∀ k : Fin d, X' * (B' k)ᴴ = μ • ((A' k)ᴴ * X') := by
    intro k
    have h' : M * (K k)ᴴ = (K k)ᴴ * (μ • M) := by simp [hEigM, hComm_M k]
    have hL : M * (K k)ᴴ = Matrix.fromBlocks 0 (X' * (B' k)ᴴ) 0 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K k)ᴴ * (μ • M) = Matrix.fromBlocks 0 (μ • ((A' k)ᴴ * X')) 0 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
            Matrix.fromBlocks_smul]
    have h_eq := hL ▸ hR ▸ h'
    exact (Matrix.fromBlocks_inj.1 h_eq).2.1
  -- === 8. Dual intertwining: X'† * (A' k)† = conj μ • (B' k)† * X'† ===
  have hμ_conj : ‖(starRingEnd ℂ) μ‖ = 1 := by rwa [Complex.norm_conj]
  have hEigMstar : Kraus.map K Mᴴ = (starRingEnd ℂ μ) • Mᴴ := by
    calc Kraus.map K Mᴴ = (Kraus.map K M)ᴴ := by
          simpa using (Kraus.map_conjTranspose (K := K) M).symm
      _ = (starRingEnd ℂ μ) • Mᴴ := by simp [hEigM, Matrix.conjTranspose_smul]
  have hKS_Ms : Kraus.map K (Mᴴᴴ * Mᴴ) = (Kraus.map K Mᴴ)ᴴ * Kraus.map K Mᴴ :=
    Kraus.ks_equality_of_peripheral_eigenvector_of_fixedPoint
      K hK_unital hrhoT_pd hrhoT_fix Mᴴ (starRingEnd ℂ μ) hEigMstar hμ_conj
  have hComm_Ms : ∀ i : Fin d, Mᴴ * (K i)ᴴ = (K i)ᴴ * Kraus.map K Mᴴ :=
    Kraus.kraus_commute_of_ks_equality K hK_unital Mᴴ hKS_Ms
  have hInter2 : ∀ k : Fin d, X'ᴴ * (A' k)ᴴ = (starRingEnd ℂ μ) • ((B' k)ᴴ * X'ᴴ) := by
    intro k
    have h' : Mᴴ * (K k)ᴴ = (K k)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) := by
      simp [hEigMstar, hComm_Ms k]
    have hL : Mᴴ * (K k)ᴴ =
        Matrix.fromBlocks 0 0 (X'ᴴ * (A' k)ᴴ) 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose]
    have hR : (K k)ᴴ * ((starRingEnd ℂ μ) • Mᴴ) =
        Matrix.fromBlocks 0 0 ((starRingEnd ℂ μ) • ((B' k)ᴴ * X'ᴴ)) 0 := by
      simp [M, K, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose,
            Matrix.fromBlocks_smul]
    have h_eq := hL ▸ hR ▸ h'
    exact (Matrix.fromBlocks_inj.1 h_eq).2.2.1
  -- === 9. ker(X') invariant under (B' k)† ===
  have hker_X' : ∀ k : Fin d, ∀ v, X' *ᵥ v = 0 → X' *ᵥ ((B' k)ᴴ *ᵥ v) = 0 := by
    intro k v hv
    have : X' *ᵥ ((B' k)ᴴ *ᵥ v) = (X' * (B' k)ᴴ) *ᵥ v := by
      simp [Matrix.mulVec_mulVec]
    rw [this, hInter1 k, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
        hv, Matrix.mulVec_zero, smul_zero]
  -- B' is injective (spanning preserved by conjugation)
  have hB' : IsInjective B' := isInjective_conjugate B hB SB hSB_det
  -- ker(X') = 0 → X' injective → D₂ ≤ D₁
  have h_D₂_le : D₂ ≤ D₁ :=
    Matrix.dim_le_of_mulVec_injective X'
      (injective_of_ker_all X' hX'ne (ker_all_of_inj B' hB' X' hker_X'))
  -- === 10. ker(X'†) invariant under (A' k)† ===
  have hX'hne : X'ᴴ ≠ 0 := by
    intro h; apply hX'ne; exact Matrix.conjTranspose_eq_zero.mp h
  have hker_X'h : ∀ k : Fin d, ∀ v, X'ᴴ *ᵥ v = 0 → X'ᴴ *ᵥ ((A' k)ᴴ *ᵥ v) = 0 := by
    intro k v hv
    have : X'ᴴ *ᵥ ((A' k)ᴴ *ᵥ v) = (X'ᴴ * (A' k)ᴴ) *ᵥ v := by
      simp [Matrix.mulVec_mulVec]
    rw [this, hInter2 k, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
        hv, Matrix.mulVec_zero, smul_zero]
  -- A' is injective (spanning preserved by conjugation)
  have hA' : IsInjective A' := isInjective_conjugate A hA SA hSA_det
  -- ker(X'†) = 0 → X'† injective → D₁ ≤ D₂
  have h_D₁_le : D₁ ≤ D₂ :=
    Matrix.dim_le_of_mulVec_injective X'ᴴ
      (injective_of_ker_all X'ᴴ hX'hne (ker_all_of_inj A' hA' X'ᴴ hker_X'h))
  -- === 11. Conclusion ===
  exact le_antisymm h_D₁_le h_D₂_le

end DimensionEquality

/-! ## Main theorem -/

section MainTheorem

/-- **Dimension-mismatch spectral gap**: the spectral radius of the rectangular mixed transfer
operator is strictly less than 1 when the bond dimensions differ. -/
theorem mixedTransferSpectralRadius₂_lt_one_of_dim_ne
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    mixedTransferSpectralRadius₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B < 1 := by
  classical
  have hle :
      mixedTransferSpectralRadius₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B ≤ 1 :=
    spectralRadius_mixedTransfer₂_le_one (A := A) (B := B) hA_norm hB_norm
  refine lt_of_le_of_ne hle ?_
  intro hEq
  -- Set `F` to be the continuous-linear version of the mixed transfer map.
  rw [mixedTransferSpectralRadius₂_eq] at hEq
  set F : (Matrix (Fin D₁) (Fin D₂) ℂ) →L[ℂ] Matrix (Fin D₁) (Fin D₂) ℂ :=
    (Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ)) (mixedTransferMap₂ A B)
  have hEqF : spectralRadius ℂ F = 1 := by simpa [F] using hEq
  -- If `spectralRadius = 1`, pick `μ ∈ spectrum` with `‖μ‖ = 1`.
  obtain ⟨μ, hμ_spec, hμ_rad⟩ := spectrum.exists_nnnorm_eq_spectralRadius (a := F)
  have hμ_one : (↑‖μ‖₊ : ENNReal) = 1 := by simpa [hEqF] using hμ_rad
  have hμ_nnn : ‖μ‖₊ = (1 : NNReal) := (ENNReal.coe_eq_one).1 hμ_one
  have hμ_norm : ‖μ‖ = 1 := by
    have : (‖μ‖₊ : ℝ) = (1 : ℝ) := by exact_mod_cast hμ_nnn
    simpa [coe_nnnorm] using this
  -- Convert `μ ∈ spectrum` to an eigenvalue of the linear map `mixedTransferMap₂ A B`.
  have h_spec :=
    AlgEquiv.spectrum_eq
      (Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ)) (mixedTransferMap₂ A B)
  have hμ_spec' : μ ∈ spectrum ℂ (mixedTransferMap₂ A B) := by
    have : μ ∈ spectrum ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D₁) (Fin D₂) ℂ))
          (mixedTransferMap₂ A B)) := by
      simpa [F] using hμ_spec
    simpa [h_spec] using this
  have hHas : Module.End.HasEigenvalue (mixedTransferMap₂ A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec'
  obtain ⟨X, hX_mem, hX_ne⟩ := hHas.exists_hasEigenvector
  have hFX : mixedTransferMap₂ A B X = μ • X :=
    (Module.End.mem_eigenspace_iff).1 hX_mem
  -- A modulus-one eigenvalue forces `D₁ = D₂`, contradicting `hD`.
  have hDim : D₁ = D₂ :=
    dim_eq_of_modulus_one_eigenvector (A := A) (B := B)
      hA hB hA_norm hB_norm X μ hFX hμ_norm hX_ne
  exact hD hDim

/-- **Overlap decay for dimension-mismatched tensors**: `mpvOverlap A B N → 0` when `D₁ ≠ D₂`. -/
theorem mpvOverlap_tendsto_zero_of_dim_ne
    {d D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hD : D₁ ≠ D₂) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  have hlt := mixedTransferSpectralRadius₂_lt_one_of_dim_ne A B hA hB hA_norm hB_norm hD
  exact mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one A B hlt

end MainTheorem

end MPSTensor
