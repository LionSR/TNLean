/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.Spectral.MixedTransfer
import MPSLean.QuantumPerronFrobenius
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Spectral gap for the mixed transfer operator

The key analytic ingredient: if a linear operator on a finite-dimensional
space has spectral radius strictly less than 1, then its iterates converge
to zero. This is the mechanism by which the mixed transfer operator
`F_{AB}` for distinct blocks `A ≠ B` decays, enabling block separation.

## Main results

* `eigenvalue_norm_le_one`: every eigenvalue of `F_{AB}` has modulus ≤ 1
* `spectralRadius_mixedTransfer_le_one`: `ρ(F_{AB}) ≤ 1` for normalized tensors
* `spectralRadius_mixedTransfer_lt_one`: strict spectral gap for non-equivalent blocks
* `mixedTransfer_pow_tendsto_zero`: `F_{AB}^n → 0` for distinct blocks

## References

* [PerezGarcia2007String] Pérez-García, Verstraete, Wolf, Cirac,
  *Matrix Product State Representations*, 2007.
* [Evans1978Spectral] Evans, Hanche-Olsen, *Spectral properties of positive
  maps on C*-algebras*, 1978.
-/

open scoped Matrix ComplexOrder BigOperators NNReal ENNReal

namespace MPSTensor

variable {d D : ℕ}

section SpectralConvergence

/-! ### Normed algebra structure on matrices -/

noncomputable scoped instance : NormedRing (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedRing

noncomputable scoped instance : NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAlgebra

/-! ### Spectral radius of the mixed transfer operator -/

/-- The **spectral radius** of the mixed transfer operator. -/
noncomputable def mixedTransferSpectralRadius (A B : MPSTensor d D) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B))

/-! ### Frobenius norm squared -/

/-- Frobenius norm squared of a matrix: `tr(X† X).re`. -/
noncomputable def frobSq (X : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (Matrix.trace (Xᴴ * X)).re

lemma frobSq_nonneg (X : Matrix (Fin D) (Fin D) ℂ) : 0 ≤ frobSq X :=
  (Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

private lemma complex_mul_star_re (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  rw [show star z = starRingEnd ℂ z from rfl, Complex.mul_conj', ← Complex.ofReal_pow]
  exact Complex.ofReal_re _

lemma frobSq_eq_sum (X : Matrix (Fin D) (Fin D) ℂ) :
    frobSq X = ∑ i : Fin D, ∑ j : Fin D, ‖X i j‖ ^ 2 := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [show (∑ i, ∑ j, star (X j i) * X j i) =
      (∑ j, ∑ i, star (X j i) * X j i) from Finset.sum_comm]
  simp only [Complex.re_sum]; congr 1; ext i; congr 1; ext j
  rw [mul_comm, complex_mul_star_re]

lemma frobSq_eq_zero_iff (X : Matrix (Fin D) (Fin D) ℂ) : frobSq X = 0 ↔ X = 0 := by
  rw [frobSq_eq_sum]; constructor
  · intro h; ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => by positivity).mp h i (Finset.mem_univ _)
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).mp this j
      (Finset.mem_univ _)
    rwa [sq_eq_zero_iff, norm_eq_zero] at this
  · rintro rfl; simp

lemma frobSq_pos_of_ne_zero (X : Matrix (Fin D) (Fin D) ℂ) (hX : X ≠ 0) :
    0 < frobSq X :=
  lt_of_le_of_ne (frobSq_nonneg X) (Ne.symm (mt (frobSq_eq_zero_iff X).mp hX))

lemma frobSq_smul (c : ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    frobSq (c • X) = ‖c‖ ^ 2 * frobSq X := by
  simp only [frobSq_eq_sum, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

/-! ### Eigenvector iteration -/

/-- If `F(v) = μ • v`, then `F^n(v) = μ^n • v`. -/
lemma eigenvector_pow {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (F : V →ₗ[ℂ] V) (v : V) (μ : ℂ) (h : F v = μ • v) (n : ℕ) :
    (F ^ n) v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    change (F ^ n) (F v) = _
    rw [h, map_smul, ih, smul_smul, mul_comm]; ring_nf

/-! ### Helper lemmas for the HS contraction bound -/

private lemma sum_sandwich (A B : Matrix (Fin D) (Fin D) ℂ)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    ∑ i : Fin d, A * M i * B = A * (∑ i : Fin d, M i) * B := by
  rw [Finset.mul_sum, Finset.sum_mul]

/-- Iterated TP condition: `∑_σ evalWord(K,σ)† evalWord(K,σ) = I`. -/
lemma word_conjTranspose_mul_sum (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1) (n : ℕ) :
    ∑ σ : Fin n → Fin d,
      (evalWord K (List.ofFn σ))ᴴ * evalWord K (List.ofFn σ) = 1 := by
  induction n with
  | zero => simp [evalWord, Finset.univ_unique]
  | succ n ih =>
    rw [sum_fin_succ_eq]
    simp_rw [List.ofFn_cons, evalWord, Matrix.conjTranspose_mul,
      show ∀ A B C D : Matrix (Fin D) (Fin D) ℂ,
        A * B * (C * D) = A * (B * C) * D from fun _ _ _ _ => by simp [Matrix.mul_assoc]]
    rw [Finset.sum_comm]
    simp_rw [sum_sandwich _ _ (fun i => (K i)ᴴ * K i), hK, Matrix.mul_one]
    exact ih

/-- The standard transfer map preserves trace (for TP tensors). -/
lemma trace_transferMap (A : MPSTensor d D) (Z : Matrix (Fin D) (Fin D) ℂ)
    (hA : ∑ i : Fin d, (A i)ᴴ * A i = 1) :
    Matrix.trace (transferMap (d := d) (D := D) A Z) = Matrix.trace Z := by
  rw [transferMap_apply, Matrix.trace_sum]
  conv_lhs => arg 2; ext i; rw [show Matrix.trace (A i * Z * (A i)ᴴ) =
    Matrix.trace ((A i)ᴴ * A i * Z) from by
      rw [Matrix.trace_mul_comm (A i * Z) _, Matrix.mul_assoc]]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hA, one_mul]

/-! ### Hilbert–Schmidt contraction for the mixed transfer operator -/

private noncomputable def toES (M : Matrix (Fin D) (Fin D) ℂ) :
    EuclideanSpace ℂ (Fin D × Fin D) :=
  (EuclideanSpace.equiv (Fin D × Fin D) ℂ).symm (fun p => M p.1 p.2)

@[simp] private lemma toES_apply (M : Matrix (Fin D) (Fin D) ℂ) (p : Fin D × Fin D) :
    toES M p = M p.1 p.2 := by simp [toES, EuclideanSpace.equiv]

private lemma toES_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin D) (Fin D) ℂ) :
    toES (∑ i ∈ s, f i) = ∑ i ∈ s, toES (f i) := by
  ext p; simp [Matrix.sum_apply, Finset.sum_apply]

private lemma norm_toES_sq (M : Matrix (Fin D) (Fin D) ℂ) :
    ‖toES M‖ ^ 2 = frobSq M := by
  rw [sq, ← @inner_self_eq_norm_mul_norm ℂ]
  change RCLike.re (@inner ℂ _ _ (toES M) (toES M)) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply', toES_apply, starRingEnd_apply,
    frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [show (∑ x : Fin D × Fin D, star (M x.1 x.2) * M x.1 x.2) =
    ∑ i, ∑ j, star (M i j) * M i j from Fintype.sum_prod_type _,
    show (∑ i, ∑ j, star (M i j) * M i j) =
    ∑ j, ∑ i, star (M i j) * M i j from Finset.sum_comm]
  simp [RCLike.re_to_complex]

private lemma norm_sq_sum_mul_le (a b : Fin D → ℂ) :
    ‖∑ k, a k * b k‖ ^ 2 ≤ (∑ k, ‖a k‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_mul_le _ _)) 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

set_option maxHeartbeats 800000 in
-- Frobenius submultiplicativity needs extra heartbeats for simp_rw over double sums
private lemma frobSq_mul_le (A B : Matrix (Fin D) (Fin D) ℂ) :
    frobSq (A * B) ≤ frobSq A * frobSq B := by
  simp only [frobSq_eq_sum, Matrix.mul_apply]
  calc ∑ i, ∑ j, ‖∑ k, A i k * B k j‖ ^ 2
      ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_sq_sum_mul_le _ _
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by congr 1; exact Finset.sum_comm

private lemma norm_toES_mul_le (A B : Matrix (Fin D) (Fin D) ℂ) :
    ‖toES (A * B)‖ ≤ ‖toES A‖ * ‖toES B‖ := by
  have h : ‖toES (A * B)‖ ^ 2 ≤ (‖toES A‖ * ‖toES B‖) ^ 2 := by
    rw [norm_toES_sq, mul_pow, norm_toES_sq, norm_toES_sq]; exact frobSq_mul_le A B
  nlinarith [Real.sqrt_le_sqrt h, Real.sqrt_sq (norm_nonneg (toES (A * B))),
    Real.sqrt_sq (mul_nonneg (norm_nonneg (toES A)) (norm_nonneg (toES B)))]

private lemma trace_cycle_for_frobSq (w v : Matrix (Fin D) (Fin D) ℂ) :
    (w * vᴴ * (v * wᴴ)).trace = (wᴴ * w * (vᴴ * v)).trace := by
  rw [Matrix.mul_assoc w vᴴ _, ← Matrix.mul_assoc vᴴ v wᴴ,
      ← Matrix.mul_assoc w (vᴴ * v) wᴴ,
      Matrix.trace_mul_comm (w * (vᴴ * v)) wᴴ,
      ← Matrix.mul_assoc wᴴ w (vᴴ * v)]

private lemma sum_frobSq_right (B : MPSTensor d D) (hB : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (v : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq (v * (evalWord B (List.ofFn σ))ᴴ) = frobSq v := by
  simp only [frobSq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  conv_lhs => arg 2; ext σ; rw [trace_cycle_for_frobSq (evalWord B (List.ofFn σ)) v]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul,
      word_conjTranspose_mul_sum B hB n, Matrix.one_mul]

private lemma sum_frobSq_words (K : MPSTensor d D) (hK : ∑ i : Fin d, (K i)ᴴ * K i = 1)
    (n : ℕ) :
    ∑ σ : Fin n → Fin d, frobSq (evalWord K (List.ofFn σ)) = (D : ℝ) := by
  simp only [frobSq]
  rw [← Complex.re_sum, ← Matrix.trace_sum, word_conjTranspose_mul_sum K hK n]
  simp [Matrix.trace_one, Fintype.card_fin]

set_option maxHeartbeats 1600000 in
-- The uniform bound proof chains triangle + CS + Frobenius submult over word sums
/-- **Uniform Frobenius-norm bound**: `‖F_{AB}^n(X)‖_F² ≤ D² · ‖X‖_F²`. -/
private lemma hs_contraction_mixedTransfer [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) (n : ℕ) :
    frobSq (((mixedTransferMap A B) ^ n) X) ≤ (D : ℝ) ^ 2 * frobSq X := by
  rw [mixedTransferMap_pow_apply, show (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * X * (evalWord B (List.ofFn σ))ᴴ) =
    (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) from by
    congr 1; ext σ; rw [Matrix.mul_assoc]]
  rw [show frobSq (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ)) =
    ‖toES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ^ 2 from
    (norm_toES_sq _).symm]
  set fA := fun σ : Fin n → Fin d => ‖toES (evalWord A (List.ofFn σ))‖ with hfA_def
  set fB := fun σ : Fin n → Fin d => ‖toES (X * (evalWord B (List.ofFn σ))ᴴ)‖ with hfB_def
  have h_chain : ‖toES (∑ σ : Fin n → Fin d,
    evalWord A (List.ofFn σ) * (X * (evalWord B (List.ofFn σ))ᴴ))‖ ≤
    ∑ σ : Fin n → Fin d, fA σ * fB σ :=
    ((by rw [toES_finset_sum]; exact norm_sum_le _ _) : ‖toES _‖ ≤ _).trans
      (Finset.sum_le_sum fun σ _ => norm_toES_mul_le _ _)
  have h_A : ∑ σ : Fin n → Fin d, fA σ ^ 2 = (D : ℝ) := by
    simp_rw [hfA_def, norm_toES_sq]; exact sum_frobSq_words A hA_norm n
  have h_B : ∑ σ : Fin n → Fin d, fB σ ^ 2 = frobSq X := by
    simp_rw [hfB_def, norm_toES_sq]; exact sum_frobSq_right B hB_norm X n
  calc ‖toES _‖ ^ 2
      ≤ (∑ σ : Fin n → Fin d, fA σ * fB σ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_chain 2
    _ ≤ (∑ σ, fA σ ^ 2) * (∑ σ, fB σ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ fA fB
    _ = (D : ℝ) * frobSq X := by rw [h_A, h_B]
    _ ≤ (D : ℝ) ^ 2 * frobSq X := by
        nlinarith [sq_nonneg ((D : ℝ) - 1), frobSq_nonneg X,
          show (1 : ℝ) ≤ D from by exact_mod_cast NeZero.one_le (n := D)]

/-! ### Eigenvalue bound -/

/-- **Every eigenvalue of the mixed transfer operator has modulus ≤ 1.** -/
theorem eigenvalue_norm_le_one [NeZero D]
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mixedTransferMap A B) μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ.exists_hasEigenvector
  have hFv := Module.End.mem_eigenspace_iff.mp hv_mem
  by_contra h_gt; push_neg at h_gt
  have h_pos := frobSq_pos_of_ne_zero v hv_ne
  have h_bound : ∀ n : ℕ, ‖μ‖ ^ (2 * n) ≤ (D : ℝ) ^ 2 := fun n => by
    have h1 := hs_contraction_mixedTransfer A B v hA_norm hB_norm n
    rw [eigenvector_pow _ v μ hFv n, frobSq_smul, norm_pow] at h1
    calc ‖μ‖ ^ (2 * n) = (‖μ‖ ^ n) ^ 2 := by ring
    _ ≤ _ := le_of_mul_le_mul_right (by linarith) h_pos
  have htend := tendsto_pow_atTop_atTop_of_one_lt (by nlinarith : 1 < ‖μ‖ ^ 2)
  rw [Filter.tendsto_atTop_atTop] at htend
  obtain ⟨n, hn⟩ := htend ((D : ℝ) ^ 2 + 1)
  linarith [h_bound n, show (‖μ‖ ^ 2) ^ n = ‖μ‖ ^ (2 * n) from by ring, hn n le_rfl]

/-- **Spectral radius bound**: `ρ(F_{AB}) ≤ 1` for normalized tensors. -/
theorem spectralRadius_mixedTransfer_le_one
    (A B : MPSTensor d D)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    mixedTransferSpectralRadius A B ≤ 1 := by
  unfold mixedTransferSpectralRadius
  rcases eq_or_ne D 0 with rfl | hD
  · have : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := ⟨fun a b => by ext i; exact i.elim0⟩
    have : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ →L[ℂ] Matrix (Fin 0) (Fin 0) ℂ) :=
      ContinuousLinearMap.uniqueOfLeft.instSubsingleton
    rw [spectrum.SpectralRadius.of_subsingleton]; exact zero_le _
  · haveI : NeZero D := ⟨hD⟩
    have h_spec := AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap
      (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B)
    apply iSup₂_le; intro k hk
    rw [ENNReal.coe_le_one_iff]
    exact_mod_cast eigenvalue_norm_le_one A B hA_norm hB_norm k
      (Module.End.hasEigenvalue_iff_mem_spectrum.mpr (h_spec ▸ hk))

/-! ### Helper lemmas for the eigenvalue rigidity theorem -/

/-
**Eigenvector implies gauge** (the algebraic core of eigenvalue rigidity).

If `∑ A_i X B_i† = μX` where `X ≠ 0`, `|μ| = 1`, both tensors are injective
and normalized, then `A` and `B` are gauge-phase equivalent.

Proof strategy:

1. **X is invertible**: The kernel of X is invariant under all B_i†
   (from `∑ A_i X B_i† = μX` and `∑ A_i† A_i = I`). By injectivity of B,
   the B_i† span all matrices, so ker(X) is invariant under everything.
   If ker(X) ≠ {0}, then X = 0, contradiction.

2. **Per-index relation**: Set `C_i = X⁻¹ A_i X`. From the eigenvector equation,
   `∑ C_i B_i† = μI`. By Cauchy-Schwarz on the Hilbert-Schmidt inner product:
   `D² = |tr(∑ C_i B_i†)|² = |∑⟨B_i, C_i⟩|² ≤ (∑‖C_i‖²)(∑‖B_i‖²) = tr(∑C_i†C_i)·D`.
   So `tr(∑ C_i†C_i) ≥ D`. Also `∑(C_i - μB_i)†(C_i - μB_i) = ∑C_i†C_i - I ≥ 0`
   (the trace computation uses `∑B_i†B_i = I` and `∑C_iB_i† = μI`).
   Together with `E_A(XX†) = XX†` (which follows from QPF theory applied to
   the unique PD fixed point of the transfer map), one obtains
   `tr(∑C_i†C_i) = D`, so the PSD matrix `∑(C_i - μB_i)†(C_i - μB_i)` has
   trace 0, forcing `C_i = μB_i` for each i, i.e., `B_i = μ⁻¹X⁻¹A_iX`.

References:
* Pérez-García et al., Matrix Product State Representations (2007), Lemma 5
* Wolf, Quantum Channels & Operations (2012), §6.2
-/

/-- If ker(X) is B†-invariant and B is injective, then ker(X) is
invariant under ALL matrices (adapted from QPF/PosDef.lean).

This is a fully proved helper lemma — no sorry. It shows that if a subspace
(ker X) is invariant under all generators Bₖ†, and B spans all matrices,
then ker(X) is invariant under every matrix. -/
private lemma ker_X_all_of_inj
    (B : MPSTensor d D) (hB : IsInjective B)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ k : Fin d, ∀ v, X *ᵥ v = 0 → X *ᵥ ((B k)ᴴ *ᵥ v) = 0) :
    ∀ (M : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ),
      X *ᵥ v = 0 → X *ᵥ (M *ᵥ v) = 0 := by
  intro M v hv
  -- M† is in span of {B k}, so M†† = M is in span of {(B k)†}
  suffices ∀ N : Matrix (Fin D) (Fin D) ℂ, X *ᵥ (Nᴴ *ᵥ v) = 0 by
    specialize this Mᴴ; rwa [Matrix.conjTranspose_conjTranspose] at this
  intro N
  have hN : N ∈ Submodule.span ℂ (Set.range B) := hB ▸ Submodule.mem_top
  induction hN using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact h k v hv
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Matrix.conjTranspose_add, Matrix.add_mulVec, Matrix.mulVec_add, ha, hb, add_zero]
  | smul c a _ ha =>
    rw [Matrix.conjTranspose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, ha, smul_zero]

/-- If X ≠ 0 and ker(X) is invariant under all matrices, then det(X) ≠ 0.

Fully proved (no sorry). The idea: pick v ≠ 0 with Xv = 0, map v to
any w via a rank-1 matrix M with Mv = w, then Xw = X(Mv) = 0, so X = 0. -/
private lemma det_ne_zero_of_ker_all [NeZero D]
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X ≠ 0)
    (h_all : ∀ M : Matrix (Fin D) (Fin D) ℂ, ∀ v, X *ᵥ v = 0 → X *ᵥ (M *ᵥ v) = 0) :
    X.det ≠ 0 := by
  by_contra h_det
  rw [Matrix.exists_mulVec_eq_zero_iff.symm] at h_det
  obtain ⟨v, hv_ne, hv⟩ := h_det
  -- v ≠ 0 and Xv = 0; we'll show Xw = 0 for all w, hence X = 0
  have h_surj : ∀ w : Fin D → ℂ, X *ᵥ w = 0 := by
    intro w
    -- find some k with v k ≠ 0
    have ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h_all_zero; push_neg at h_all_zero
      exact hv_ne (funext h_all_zero)
    let c : Fin D → ℂ := fun j => if j = k then (v k)⁻¹ else 0
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
    rw [show (0 : Matrix (Fin D) (Fin D) ℂ) i j = 0 from rfl]
    rw [← this]; exact congr_fun h_ej i
  exact hX h_X_zero

-- From hFX and X invertible, derive ∑ (X⁻¹ A_i X) * B_i† = μ • 1
-- Fully proved (no sorry).
private lemma sum_conj_mul_conjTranspose [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hFX : mixedTransferMap A B X = μ • X)
    (hdet : X.det ≠ 0) :
    ∑ i : Fin d, (X⁻¹ * A i * X) * (B i)ᴴ = μ • 1 := by
  have hFX' : ∑ i : Fin d, A i * X * (B i)ᴴ = μ • X := by
    rw [← mixedTransferMap_apply]; exact hFX
  have hXinv : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X (Ne.isUnit hdet)
  have key : X⁻¹ * (∑ i : Fin d, A i * X * (B i)ᴴ) = μ • 1 := by
    rw [hFX', Matrix.mul_smul, hXinv]
  rw [Finset.mul_sum] at key
  convert key using 1; congr 1; ext i; simp [Matrix.mul_assoc]

-- If ∑ Rᵢ† Rᵢ = 0 then each Rᵢ = 0.
-- Fully proved (no sorry). Uses PSD trace argument.
private lemma each_zero_of_sum_conjTranspose_mul_self_zero
    (R : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h : ∑ i : Fin d, (R i)ᴴ * R i = 0) :
    ∀ i : Fin d, R i = 0 := by
  intro i
  have h_psd_i := Matrix.posSemidef_conjTranspose_mul_self (R i)
  have h_each_nonneg : ∀ j, 0 ≤ ((R j)ᴴ * R j).trace.re :=
    fun j => (Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self (R j)).trace_nonneg).1
  have h_tr_sum_re : (∑ j : Fin d, ((R j)ᴴ * R j).trace.re) = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, h]; simp
  have h_tr_re : ((R i)ᴴ * R i).trace.re = 0 :=
    le_antisymm
      (by linarith [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_each_nonneg j)
            |>.mp h_tr_sum_re i (Finset.mem_univ i)])
      (h_each_nonneg i)
  have h_tr_zero : ((R i)ᴴ * R i).trace = 0 :=
    Complex.ext h_tr_re (Complex.le_def.mp h_psd_i.trace_nonneg).2.symm
  exact Matrix.conjTranspose_mul_self_eq_zero.mp (h_psd_i.trace_eq_zero_iff.mp h_tr_zero)

/-- **Step 1 — Eigenvector invertibility** (PGVWC 2007; Wolf 2012, §6.2).

If `F_{AB}(X) = μX` where `X ≠ 0`, `|μ| = 1`, both tensors are injective
and normalized, then `X` is invertible (`det(X) ≠ 0`).

**Proof sketch**: The kernel of `X` is invariant under all `Bₖ†`.
Pass to the doubly-stochastic gauge `A'ᵢ = σ⁻¹ᐟ² Aᵢ σ¹ᐟ²` where
`σ` is the unique PD fixed point of `E_A(Y) = ∑ AᵢYAᵢ†`. The transformed
channel is unital (`∑ A'ᵢ(A'ᵢ)† = I`). The Kadison-Schwarz equality
condition (from `|μ| = 1`) forces kernel invariance. Since B is injective,
`ker(X)` is invariant under ALL matrices. If ker(X) ≠ {0} then X = 0, contradiction.

**Required infrastructure** (not yet formalized):
- Doubly-stochastic gauge (uses `σ^{1/2}` from `QPF/Uniqueness.lean`)
- Kadison-Schwarz equality ⟺ multiplicative domain (~200 lines) -/
private lemma eigenvector_det_ne_zero [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    X.det ≠ 0 := by
  sorry

/-- **Step 2 — Per-index relation** (PGVWC 2007, Lemma 5; Wolf 2012, §6.2).

If `F_{AB}(X) = μX` where `X` is invertible, `|μ| = 1`, and both tensors
are injective and normalized, then `Bᵢ = μ̄ · X⁻¹AᵢX` for each `i`.

**Proof sketch**: Set `Cᵢ = X⁻¹AᵢX` and `Dᵢ = μ̄Cᵢ`. From the eigenvector
equation, `∑ DᵢBᵢ† = I`. The PSD matrix `∑(Dᵢ - Bᵢ)†(Dᵢ - Bᵢ)` has
`trace = ∑‖Cᵢ‖²_F - D`. In the doubly-stochastic gauge (using the QPF
fixed point `σ`), the KS equality condition forces `∑‖Cᵢ‖² = D`, so the
PSD trace is 0, giving `Dᵢ = Bᵢ` for each `i`.

**Required infrastructure** (not yet formalized):
- Doubly-stochastic gauge + Kadison-Schwarz equality → ∑‖Cᵢ‖² = D (~200 lines)
- Alternative: PGVWC OBC approach (quant-ph/0608197, Lemma 5) -/
private lemma per_index_from_eigenvector [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hdet : X.det ≠ 0) :
    ∀ i : Fin d, B i = starRingEnd ℂ μ • (X⁻¹ * A i * X) := by
  sorry

/-- **Eigenvector implies gauge equivalence** (PGVWC 2007, Lemma 5; Wolf 2012, §6.2).

If `F_{AB}(X) = μX` where `X ≠ 0`, `|μ| = 1`, both tensors are injective
and normalized, then `A` and `B` are gauge-phase equivalent.

Assembled from `eigenvector_det_ne_zero` (Step 1) and
`per_index_from_eigenvector` (Step 2). The assembly is fully proved.

**Available helper lemmas** (fully proved, no sorry):
- `ker_X_all_of_inj`: B†-kernel invariance → total kernel invariance
- `det_ne_zero_of_ker_all`: total kernel invariance + X ≠ 0 → det(X) ≠ 0
- `sum_conj_mul_conjTranspose`: eigenvector eq + X invertible → `∑ CᵢBᵢ† = μI`
- `each_zero_of_sum_conjTranspose_mul_self_zero`: `∑ Rᵢ†Rᵢ = 0 → Rᵢ = 0` -/
private lemma eigenvector_gives_gauge [NeZero D]
    (A B : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) (μ : ℂ)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hFX : mixedTransferMap A B X = μ • X)
    (hμ : ‖μ‖ = 1) (hX : X ≠ 0) :
    GaugePhaseEquiv A B := by
  have hdet := eigenvector_det_ne_zero A B X μ hA hB hA_norm hB_norm hFX hμ hX
  have hpi := per_index_from_eigenvector A B X μ hA hB hA_norm hB_norm hFX hμ hdet
  exact ⟨(Matrix.nonsingInvUnit X (Ne.isUnit hdet))⁻¹, starRingEnd ℂ μ, fun i => (hpi i)⟩

/-- **Eigenvalue rigidity** (Pérez-García et al. 2007, Lemma 5):
if the mixed transfer spectral radius is ≥ 1, then A and B are
gauge-phase equivalent. -/
theorem modulus_one_eigenvalue_implies_gauge
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B := by
  -- Edge case: D = 0
  rcases eq_or_ne D 0 with rfl | hD
  · -- For D = 0, all matrices are trivially equal; any GL element works
    exact ⟨1, 1, fun i => by ext a; exact a.elim0⟩
  haveI : NeZero D := ⟨hD⟩
  -- Step 1: Extract eigenvalue with |μ| = 1 and eigenvector X ≠ 0
  -- The spectral radius equals 1 (≥ 1 from hypothesis, ≤ 1 already proved)
  set V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  haveI : Nontrivial V := by
    haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
    exact Matrix.nonempty
  haveI : Nontrivial (V →L[ℂ] V) := ContinuousLinearMap.instNontrivialId
  -- Spectral radius is achieved
  obtain ⟨μ, hμ_spec, hμ_norm⟩ := spectrum.exists_nnnorm_eq_spectralRadius F'
  -- Transfer to eigenvalue of the linear map
  have h_spec_eq := AlgEquiv.spectrum_eq Φ (mixedTransferMap A B)
  have hμ_spec_end : μ ∈ spectrum ℂ (mixedTransferMap A B) := h_spec_eq ▸ hμ_spec
  have hμ_ev : Module.End.HasEigenvalue (mixedTransferMap A B) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ_spec_end
  obtain ⟨X, hX_mem, hX_ne⟩ := hμ_ev.exists_hasEigenvector
  have hFX : mixedTransferMap A B X = μ • X := Module.End.mem_eigenspace_iff.mp hX_mem
  -- Step 2: Show |μ| = 1
  have hμ_le : ‖μ‖ ≤ 1 := eigenvalue_norm_le_one A B hA_norm hB_norm μ hμ_ev
  have hμ_ge : (1 : ℝ≥0∞) ≤ ‖μ‖₊ := by rw [hμ_norm]; exact hsr
  have hμ_eq : ‖μ‖ = 1 := le_antisymm hμ_le (by
    rw [ENNReal.one_le_coe_iff] at hμ_ge; exact_mod_cast hμ_ge)
  -- Step 3: Apply the core algebraic lemma
  exact eigenvector_gives_gauge A B X μ hA hB hA_norm hB_norm hFX hμ_eq hX_ne

/-- **Spectral gap for distinct blocks**: `ρ(F_{AB}) < 1` when `A ≇ B`. -/
theorem spectralRadius_mixedTransfer_lt_one
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    mixedTransferSpectralRadius A B < 1 :=
  lt_of_le_of_ne (spectralRadius_mixedTransfer_le_one A B hA_norm hB_norm)
    fun h => hAB (modulus_one_eigenvalue_implies_gauge A B hA hB hA_norm hB_norm h.ge)

/-! ### Power convergence from spectral radius bound -/

/-- **Powers tend to zero when spectral radius < 1.** -/
theorem pow_tendsto_zero_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A]
    (a : A) (h : spectralRadius ℂ a < 1) :
    Filter.Tendsto (fun n => a ^ n) Filter.atTop (nhds 0) := by
  obtain ⟨r, hr_above, hr_below⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hr_lt_one : r < 1 := ENNReal.coe_lt_coe.mp (by rwa [ENNReal.coe_one])
  have hev2 : ∀ᶠ n in Filter.atTop, ‖a ^ n‖₊ < r ^ n := by
    have gelfand := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
    filter_upwards [gelfand.eventually (eventually_lt_nhds hr_above),
      Filter.eventually_gt_atTop 0] with n hn hn_pos
    rw [one_div, ENNReal.rpow_inv_lt_iff (Nat.cast_pos.mpr hn_pos)] at hn
    rw [ENNReal.rpow_natCast] at hn
    exact_mod_cast hn
  apply squeeze_zero_norm' (a := fun n => (r : ℝ) ^ n)
  · filter_upwards [hev2] with n hn
    rw [← coe_nnnorm, ← NNReal.coe_pow]; exact_mod_cast hn.le
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg (by exact_mod_cast hr_lt_one)

/-! ### Application to mixed transfer convergence -/

/-- **Mixed transfer iterates decay for distinct blocks**: `F_{AB}^n(X) → 0`. -/
theorem mixedTransfer_pow_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    Filter.Tendsto (fun n => ((mixedTransferMap A B) ^ n) X)
      Filter.atTop (nhds 0) := by
  let V := Matrix (Fin D) (Fin D) ℂ
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap A B)
  have h_clm : Filter.Tendsto (fun n => F' ^ n) Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one F'
      (spectralRadius_mixedTransfer_lt_one A B hA hB hA_norm hB_norm hAB)
  have h_eval := (ContinuousLinearMap.apply ℂ V X).continuous.tendsto (0 : V →L[ℂ] V)
  rw [map_zero] at h_eval
  suffices ∀ n, ((mixedTransferMap A B) ^ n) X = (F' ^ n) X by
    simp_rw [this]; exact h_eval.comp h_clm
  intro n
  have h_pow : F' ^ n = Φ ((mixedTransferMap A B) ^ n) := (map_pow Φ _ n).symm
  simp only [h_pow]; rfl

end SpectralConvergence

end MPSTensor
