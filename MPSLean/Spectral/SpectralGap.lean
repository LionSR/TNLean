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

/-! ### Transfer matrix (vectorized transfer operator) -/

/-- The **transfer matrix**: `T_AB = ∑_k A^k ⊗ conj(B^k)`. -/
noncomputable def transferMatrix (A B : MPSTensor d D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ∑ k : Fin d, Matrix.kroneckerMap (· * ·) (A k) (star (B k))

/-- The transfer matrix for `A = B` is the standard self-transfer matrix. -/
theorem transferMatrix_self (A : MPSTensor d D) :
    transferMatrix A A = ∑ k : Fin d, Matrix.kroneckerMap (· * ·) (A k) (star (A k)) :=
  rfl

/-! ### Spectral radius of the mixed transfer operator -/

/-- The **spectral radius** of the mixed transfer operator. -/
noncomputable def mixedTransferSpectralRadius (A B : MPSTensor d D) : ENNReal :=
  spectralRadius ℂ
    ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mixedTransferMap A B))

/-- The spectral radius of the mixed transfer operator equals
the spectral radius of the vectorized transfer matrix. -/
theorem mixedTransferSpectralRadius_eq_transferMatrix
    (A B : MPSTensor d D) :
    mixedTransferSpectralRadius A B =
      (⨆ k ∈ spectrum ℂ (transferMatrix A B), (‖k‖₊ : ENNReal)) := by
  sorry

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

/-- **Eigenvalue rigidity** (Pérez-García et al. 2007, Lemma 5). -/
axiom modulus_one_eigenvalue_implies_gauge
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hsr : mixedTransferSpectralRadius A B ≥ 1) :
    GaugePhaseEquiv A B

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
