/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RepeatedOverlappingBlockWeights
import TNLean.MPS.Preparation.PolarCompression

/-!
# The diagonal deficit of the relative polar columns

For a direct sum of normal tensors with nonzero copy weights, let `P` be the positive
factor of a blocked tensor, and let `L_j` be the orthogonal copy isometries. The relative
column blocks are `H_kj = L_kᴴ P L_j / c_j`, where `c_j` is the norm of the weights in
column `j`. Their Gram sum equals the Gram matrix of the unweighted blocked component.
Thus their weighted squared norms sum to one.

The diagonal coefficient `α_j` against the fixed-point tensor is nonnegative. Its exact
normalization deficit is half the sum of the squared diagonal error and the squared norms
of the other column blocks. Consequently a first-order bound on all relative columns
implies a second-order bound on `1 - α_j`, with constants independent of the copy weights.

These are project refinements of the normalized-state approximation in arXiv:2307.01696,
Supplemental Material, Lemma 1′(ii), eqs. `eq:B_TM` and `eq:fid_err_gen_non_normal`. They do not
assert a quadratic rate for the norm of the positive factor itself. When the subleading
spectral bound is zero, the final displayed exponential is constant under the convention
`correlationLength 0 = 0`; exact finite-block stabilization is a separate result.

**Local fix (multiplicity copies):** The copy isometries and relative columns use the
corrected repeated-block approximation, in which copy weights are summed within each normal block.
This correction and the distinction between matrix-norm and normalized-state rates are
recorded in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex` and
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder Kronecker InnerProductSpace

noncomputable section

namespace MPSTensor

variable {b : ℕ} {κ : Fin b → Type*} [∀ k, Fintype (κ k)]
  {n : Type*} [Fintype n]

/-- The column blocks of a supported matrix recover its Gram matrix. -/
private theorem column_gram (L : (k : Fin b) → Matrix n (κ k) ℂ)
    (P : Matrix n n ℂ) (hSupp : (∑ k, L k * (L k)ᴴ) * P = P)
    (j : Fin b) (s : ℝ) :
    ∑ k, ((s : ℂ) • ((L k)ᴴ * P * L j))ᴴ *
      ((s : ℂ) • ((L k)ᴴ * P * L j)) =
      ((s ^ 2 : ℝ) : ℂ) • ((L j)ᴴ * (Pᴴ * P) * L j) := by
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← Finset.smul_sum]
  have h : ∑ k, ((L j)ᴴ * (Pᴴ * L k)) * ((L k)ᴴ * P * L j) =
      (L j)ᴴ * (Pᴴ * P) * L j := by
    calc
      _ = (L j)ᴴ * Pᴴ * (∑ k, L k * (L k)ᴴ) * P * L j := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = (L j)ᴴ * (Pᴴ * P) * L j := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (∑ k, L k * (L k)ᴴ) P (L j), hSupp]
  rw [h]
  norm_cast
  rw [sq]

omit [∀ k, Fintype (κ k)] in
/-- A positive diagonal block remains positive after division by a positive weight. -/
private theorem diagonal_posSemidef (j : Fin b) [Finite (κ j)]
    (L : Matrix n (κ j) ℂ) {P : Matrix n n ℂ}
    (hP : P.PosSemidef) {c : ℝ} (hc : 0 < c) :
    (((c : ℂ)⁻¹) • (Lᴴ * P * L)).PosSemidef := by
  exact (hP.conjTranspose_mul_mul_same L).smul
    (by simpa using (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le)))

variable {p : Type*} [Fintype p]

/-- The normalized columns of a polar factor retain the original component Gram matrix. -/
private theorem polar_column_gram [DecidableEq n] [∀ k, DecidableEq (κ k)]
    (L : (k : Fin b) → Matrix n (κ k) ℂ)
    (B : (k : Fin b) → Matrix p (κ k) ℂ) (c : Fin b → ℝ)
    (hc : ∀ k, 0 < c k)
    (hiso : ∀ k, (L k)ᴴ * L k = 1)
    (horth : ∀ k l, k ≠ l → (L k)ᴴ * L l = 0)
    (hSupp : (∑ k, L k * (L k)ᴴ) *
      Matrix.polarPos (∑ k, (c k : ℂ) • (B k * (L k)ᴴ)) =
      Matrix.polarPos (∑ k, (c k : ℂ) • (B k * (L k)ᴴ)))
    (j : Fin b) :
    let A := ∑ k, (c k : ℂ) • (B k * (L k)ᴴ)
    let P := Matrix.polarPos A
    ∑ k, (((c j : ℂ)⁻¹) • ((L k)ᴴ * P * L j))ᴴ *
      (((c j : ℂ)⁻¹) • ((L k)ᴴ * P * L j)) = (B j)ᴴ * B j := by
  classical
  dsimp only
  let A := ∑ k, (c k : ℂ) • (B k * (L k)ᴴ)
  let P := Matrix.polarPos A
  have hQP : (∑ k, L k * (L k)ᴴ) * P = P := hSupp
  have hAL : A * L j = (c j : ℂ) • B j := by
    dsimp only [A]
    rw [Matrix.sum_mul, Finset.sum_eq_single j]
    · rw [Matrix.smul_mul, Matrix.mul_assoc, hiso, Matrix.mul_one]
    · intro k _ hkj
      rw [Matrix.smul_mul, Matrix.mul_assoc, horth k j hkj, Matrix.mul_zero, smul_zero]
    · simp
  change ∑ k, (((c j : ℂ)⁻¹) • ((L k)ᴴ * P * L j))ᴴ *
      (((c j : ℂ)⁻¹) • ((L k)ᴴ * P * L j)) = _
  have hG := column_gram L P hQP j (c j)⁻¹
  simp only [Complex.ofReal_inv] at hG
  rw [hG, (Matrix.posSemidef_polarPos A).isHermitian.eq,
    Matrix.polarPos_mul_polarPos]
  have h : (L j)ᴴ * (Aᴴ * A) * L j = ((c j : ℂ)^2) • ((B j)ᴴ * B j) := by
    calc
      _ = (A * L j)ᴴ * (A * L j) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((c j : ℂ)^2) • ((B j)ᴴ * B j) := by
        rw [hAL]
        simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
  rw [h, smul_smul]
  have hc0 : (c j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hc j).ne'
  simp only [Complex.ofReal_pow, Complex.ofReal_inv, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc0),
    one_smul]

/-- The weighted energy of a tensor depends linearly on its physical Gram matrix. -/
private theorem trace_transfer_eq_gram {d D : ℕ} (X : MPSTensor d D)
    (σ : Matrix (Fin D) (Fin D) ℂ) :
    (Kraus.transferMap X σ).trace =
      ∑ a, ∑ c, ∑ t, σ c t *
        ((MPSTensor.physicalMatrix X)ᴴ * MPSTensor.physicalMatrix X) (a, t) (a, c) := by
  simp only [Kraus.mapLM_apply, Kraus.map_apply, Matrix.trace, Matrix.diag, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, MPSTensor.physicalMatrix, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc
    _ = ∑ i : Fin d, ∑ c : Fin D, ∑ t : Fin D,
        X i a c * σ c t * star (X i a t) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ c : Fin D, ∑ i : Fin d, ∑ t : Fin D,
        X i a c * σ c t * star (X i a t) := Finset.sum_comm
    _ = ∑ c : Fin D, ∑ t : Fin D, ∑ i : Fin d,
        X i a c * σ c t * star (X i a t) :=
      Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- The weighted Gram trace, as a linear functional. -/
private def weightedGramTraceLM {D : ℕ} (σ : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ →ₗ[ℂ] ℂ where
  toFun G := ∑ a, ∑ c, ∑ t, σ c t * G (a, t) (a, c)
  map_add' G H := by simp [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z G := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun t _ => by ring

/-- Reading a matrix as a tensor preserves its physical Gram matrix. -/
private theorem gram_ofPhysicalMatrixLM {D E : ℕ}
    (H : Matrix (Fin E × Fin E) (Fin D × Fin D) ℂ) :
    (MPSTensor.physicalMatrix (MPSTensor.ofPhysicalMatrixLM H))ᴴ *
      MPSTensor.physicalMatrix (MPSTensor.ofPhysicalMatrixLM H) = Hᴴ * H := by
  change (H.submatrix (MPSTensor.virtualPairEquiv E) id)ᴴ *
    H.submatrix (MPSTensor.virtualPairEquiv E) id = Hᴴ * H
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]

/-- The squared weighted norm is the weighted Gram trace. -/
private theorem norm_sqrtWeight_eq_weightedGram {D E : ℕ}
    (H : Matrix (Fin E × Fin E) (Fin D × Fin D) ℂ)
    {σ : Matrix (Fin D) (Fin D) ℂ} (hσ : σ.PosSemidef) :
    ((‖MPSTensor.sqrtWeightLM σ (MPSTensor.ofPhysicalMatrixLM H)‖ ^ 2 : ℝ) : ℂ) =
      weightedGramTraceLM σ (Hᴴ * H) := by
  have h := MPSTensor.inner_sqrtWeightLM hσ
    (MPSTensor.ofPhysicalMatrixLM H) (MPSTensor.ofPhysicalMatrixLM H)
  rw [inner_self_eq_norm_sq_to_K, Kraus.mixedMapLM_self] at h
  calc
    _ = (Kraus.transferMap (MPSTensor.ofPhysicalMatrixLM H) σ).trace := by
      push_cast
      exact h
    _ = _ := by
      rw [trace_transfer_eq_gram]
      change weightedGramTraceLM σ
        ((MPSTensor.physicalMatrix (MPSTensor.ofPhysicalMatrixLM H))ᴴ *
          MPSTensor.physicalMatrix (MPSTensor.ofPhysicalMatrixLM H)) = _
      rw [gram_ofPhysicalMatrixLM]

section ActualColumns
variable {d D b : ℕ} {m Dj : Fin b → ℕ}
    {Aj : (j : Fin b) → MPSTensor d (Dj j)}
    {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- The actual relative polar columns retain the Gram matrix of the blocked component. -/
theorem relative_column_gram
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' →
      ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0) (j : Fin b) :
    ∑ k, (relativeRow (repeatedBlockSum Aj ι μ) ι μ q k j)ᴴ *
      relativeRow (repeatedBlockSum Aj ι μ) ι μ q k j =
      (physicalMatrix (blockTensor (Aj j) q))ᴴ * physicalMatrix (blockTensor (Aj j) q) := by
  have hPs := polarPos_mul_sum_copyIsometry (Aj := Aj) hι hdisj μ hq
  have hPh := (Matrix.posSemidef_polarPos
    (physicalMatrix (blockTensor (repeatedBlockSum Aj ι μ) q))).isHermitian.eq
  have hSupp := congrArg Matrix.conjTranspose hPs
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_conjTranspose, hPh] at hSupp
  rw [physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry hι hdisj hq] at hSupp
  have h := polar_column_gram (fun k => copyIsometry ι μ q k)
    (fun k => physicalMatrix (blockTensor (Aj k) q)) (copyNorm μ q)
    (fun k => copyNorm_pos (μ.weight_fun_ne_zero k) q)
    (fun k => conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero k) q)
    (fun k l hkl => conjTranspose_copyIsometry_mul_eq_zero hdisj μ q hkl) hSupp j
  dsimp only at h
  rw [← physicalMatrix_blockTensor_repeatedBlockSum_eq_copyIsometry hι hdisj hq] at h
  simp_rw [relativeRow_eq_smul hι hdisj]
  exact h

/-- The weighted norms in every actual relative polar column have total square one. -/
theorem sum_norm_relative_column_sq
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' →
      ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0) (j : Fin b)
    {σ : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap (Aj j) σ = σ) :
    ∑ k, ‖sqrtWeightLM σ (ofPhysicalMatrixLM
      (relativeRow (repeatedBlockSum Aj ι μ) ι μ q k j))‖ ^ 2 = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [norm_sqrtWeight_eq_weightedGram _ hσ]
  rw [← map_sum, relative_column_gram hι hdisj μ hq j]
  change weightedGramTraceLM σ
    ((physicalMatrix (blockTensor (Aj j) q))ᴴ * physicalMatrix (blockTensor (Aj j) q)) = (1 : ℂ)
  change (∑ a, ∑ c, ∑ t, σ c t *
    ((physicalMatrix (blockTensor (Aj j) q))ᴴ * physicalMatrix (blockTensor (Aj j) q))
      (a, t) (a, c)) = _
  rw [← trace_transfer_eq_gram, transferMap_blockTensor_apply, Module.End.pow_apply,
    Function.iterate_fixed hfix, htr]

/-- Positivity of the actual diagonal relative compression coefficient. -/
theorem relative_diagonal_nonneg
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' →
      ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) (q : ℕ) (j : Fin b)
    {σ : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ (Kraus.mixedMapLM (ofPhysicalMatrixLM
      (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j)) (fixedPointTensor σ) σ).trace := by
  rw [trace_mixedMapLM_ofPhysicalMatrixLM_fixedPointTensor]
  have hH : (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j).PosSemidef := by
    rw [relativeRow_eq_smul hι hdisj]
    exact diagonal_posSemidef (κ := fun k => Fin (Dj k) × Fin (Dj k)) j _
      (Matrix.posSemidef_polarPos _) (copyNorm_pos (μ.weight_fun_ne_zero j) q)
  exact hH.trace_mul_nonneg
    ((Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg σ)).transpose.kronecker hσ)

/-- The exact diagonal deficit includes the off-column energy lost by compression. -/
theorem relative_diagonal_geometry
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' →
      ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (μ : CopyWeights b m) {q : ℕ} (hq : q ≠ 0) (j : Fin b)
    {σ : Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (hfix : Kraus.transferMap (Aj j) σ = σ) :
    let x := fun k => sqrtWeightLM σ (ofPhysicalMatrixLM
      (relativeRow (repeatedBlockSum Aj ι μ) ι μ q k j))
    let y := sqrtWeightLM σ (fixedPointTensor σ)
    let α := (Kraus.mixedMapLM (ofPhysicalMatrixLM
      (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j)) (fixedPointTensor σ) σ).trace
    α.re ≤ 1 ∧
      1 - α.re = (‖x j - y‖ ^ 2 + ∑ k ∈ Finset.univ.erase j, ‖x k‖ ^ 2) / 2 := by
  classical
  dsimp only
  let x := fun k => sqrtWeightLM σ (ofPhysicalMatrixLM
    (relativeRow (repeatedBlockSum Aj ι μ) ι μ q k j))
  let y := sqrtWeightLM σ (fixedPointTensor σ)
  let α := (Kraus.mixedMapLM (ofPhysicalMatrixLM
    (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j)) (fixedPointTensor σ) σ).trace
  have hsum : ∑ k, ‖x k‖ ^ 2 = 1 := sum_norm_relative_column_sq hι hdisj μ hq j hσ htr hfix
  have hy : ‖y‖ = 1 := norm_sqrtWeightLM_fixedPointTensor hσ htr
  have hα : ⟪y, x j⟫_ℂ = α := inner_sqrtWeightLM hσ _ _
  have hx : ‖x j‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖x k‖) (Finset.mem_univ j)
  have hx1 : ‖x j‖ ≤ 1 := by nlinarith [norm_nonneg (x j)]
  have hre : α.re ≤ 1 := by
    calc
      α.re ≤ ‖α‖ := Complex.re_le_norm _
      _ = ‖⟪y, x j⟫_ℂ‖ := congrArg norm hα.symm
      _ ≤ ‖y‖ * ‖x j‖ := norm_inner_le_norm _ _
      _ ≤ 1 := by rw [hy, one_mul]; exact hx1
  refine ⟨hre, ?_⟩
  have hdist := @norm_sub_sq ℂ _ _ _ _ (x j) y
  have hinner : RCLike.re ⟪x j, y⟫_ℂ = α.re := by
    rw [← inner_conj_symm, RCLike.conj_re, hα]
    rfl
  rw [hy, hinner] at hdist
  have hsplit := Finset.sum_erase_add Finset.univ (fun k => ‖x k‖ ^ 2)
    (Finset.mem_univ j)
  rw [hsum] at hsplit
  change 1 - α.re = (‖x j - y‖ ^ 2 + ∑ k ∈ Finset.univ.erase j, ‖x k‖ ^ 2) / 2
  linarith
open scoped Matrix.Norms.L2Operator in
/-- A finite-dimensional constant bounds the diagonal deficit uniformly in all copy weights. -/
theorem exists_relative_diagonal_deficit_le
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' →
      ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (σ : (k : Fin b) → Matrix (Fin (Dj k)) (Fin (Dj k)) ℂ) (j : Fin b)
    (hσ : (σ j).PosSemidef) (htr : (σ j).trace = 1)
    (hfix : Kraus.transferMap (Aj j) (σ j) = σ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : CopyWeights b m) (q : ℕ), q ≠ 0 → ∀ δ : ℝ,
      (∀ k, ‖relativeRow (repeatedBlockSum Aj ι μ) ι μ q k j -
        relativeRowLimit ι μ q σ k j‖ ≤ δ) →
      let α := (Kraus.mixedMapLM (ofPhysicalMatrixLM
        (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j))
        (fixedPointTensor (σ j)) (σ j)).trace
      ‖α‖ ≤ 1 ∧ ‖1 - α‖ ≤ C * δ ^ 2 := by
  classical
  let Φ := fun k => sqrtWeightLM (σ j) ∘ₗ
    (ofPhysicalMatrixLM (D₂ := Dj k) (D := Dj j))
  let a := fun k => ‖LinearMap.toContinuousLinearMap (Φ k)‖
  let S := ∑ k, a k ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => sq_nonneg (a k)
  refine ⟨1 + S, by positivity, fun μ q hq δ hrow => ?_⟩
  let H := fun k => relativeRow (repeatedBlockSum Aj ι μ) ι μ q k j
  let Hinf := fun k => relativeRowLimit ι μ q σ k j
  let x := fun k => sqrtWeightLM (σ j) (ofPhysicalMatrixLM (H k))
  let y := sqrtWeightLM (σ j) (fixedPointTensor (σ j))
  let v := fun k => Φ k (H k - Hinf k)
  let α := (Kraus.mixedMapLM (ofPhysicalMatrixLM (H j))
    (fixedPointTensor (σ j)) (σ j)).trace
  have hnonneg : 0 ≤ α := relative_diagonal_nonneg hι hdisj μ q j hσ
  have hnorm : α.re = ‖α‖ := by
    simpa using congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hnonneg)
  have hcoef : α = (α.re : ℂ) := by
    rw [hnorm]
    exact Complex.eq_coe_norm_of_nonneg hnonneg
  obtain ⟨hre, hgeom⟩ := relative_diagonal_geometry hι hdisj μ hq j hσ htr hfix
  change α.re ≤ 1 at hre
  have hnormsub : ‖1 - α‖ = 1 - α.re := by
    calc
      _ = ‖((1 - α.re : ℝ) : ℂ)‖ := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, hcoef]
        simp only [Complex.ofReal_re]
      _ = _ := Complex.norm_of_nonneg (sub_nonneg.mpr hre)
  have hlim : ofPhysicalMatrixLM (Hinf j) = fixedPointTensor (σ j) := by
    dsimp only [Hinf]
    rw [relativeRowLimit_self hι hdisj]
    exact ofPhysicalMatrix_sqrt_transpose_kronecker_one _
  have hvj : v j = x j - y := by
    dsimp only [v, Φ, LinearMap.comp_apply, x, y]
    rw [map_sub, map_sub, hlim]
  have hvk : ∀ k, k ≠ j → v k = x k := by
    intro k hkj
    dsimp only [v, Φ, LinearMap.comp_apply, x, Hinf]
    rw [relativeRowLimit_of_ne hι hdisj μ q σ hkj, sub_zero]
  have hsumv := Finset.sum_erase_add Finset.univ (fun k => ‖v k‖ ^ 2)
    (Finset.mem_univ j)
  have hoff : (∑ k ∈ Finset.univ.erase j, ‖v k‖ ^ 2) =
      ∑ k ∈ Finset.univ.erase j, ‖x k‖ ^ 2 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hvk k (Finset.mem_erase.mp hk).1]
  rw [hoff, hvj, add_comm] at hsumv
  change 1 - α.re = (‖x j - y‖ ^ 2 + ∑ k ∈ Finset.univ.erase j, ‖x k‖ ^ 2) / 2 at hgeom
  have hv : ∀ k, ‖v k‖ ≤ a k * δ := by
    intro k
    exact ((LinearMap.toContinuousLinearMap (Φ k)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hrow k) (norm_nonneg _))
  have henergy : (∑ k, ‖v k‖ ^ 2) ≤ S * δ ^ 2 := by
    change (∑ k, ‖v k‖ ^ 2) ≤ (∑ k, a k ^ 2) * δ ^ 2
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    calc
      ‖v k‖ ^ 2 ≤ (a k * δ) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (hv k) 2
      _ = a k ^ 2 * δ ^ 2 := mul_pow _ _ _
  refine ⟨by rwa [← hnorm], ?_⟩
  rw [hnormsub, hgeom, hsumv]
  calc
    _ ≤ S * δ ^ 2 / 2 := div_le_div_of_nonneg_right henergy (by norm_num)
    _ ≤ (1 + S) * δ ^ 2 := by nlinarith [sq_nonneg δ]

open scoped Matrix.Norms.L2Operator in
/-- The actual diagonal coefficient has the second-order spectral rate uniformly in the weights. -/
theorem exists_norm_one_sub_relative_diagonal_le
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' →
      ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
    (hσ : ∀ j, (σ j).PosDef) (htr : ∀ j, (σ j).trace = 1)
    (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hl : ‖lam₂‖ < 1)
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ',
      Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) (j : Fin b) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ (μ : CopyWeights b m) (q : ℕ), q₀ ≤ q → q ≠ 0 →
      let α := (Kraus.mixedMapLM (ofPhysicalMatrixLM
        (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j))
        (fixedPointTensor (σ j)) (σ j)).trace
      ‖α‖ ≤ 1 ∧ ‖1 - α‖ ≤ C * Real.exp (-(2 * γ) * q / correlationLength lam₂) := by
  rcases eq_or_ne lam₂ 0 with h0 | h0
  · refine ⟨2, by norm_num, 1, fun μ q _ hq => ?_⟩
    dsimp only
    let α := (Kraus.mixedMapLM (ofPhysicalMatrixLM
      (relativeRow (repeatedBlockSum Aj ι μ) ι μ q j j))
      (fixedPointTensor (σ j)) (σ j)).trace
    have hnonneg : 0 ≤ α := relative_diagonal_nonneg hι hdisj μ q j (hσ j).posSemidef
    have hre : α.re ≤ 1 :=
      (relative_diagonal_geometry hι hdisj μ hq j (hσ j).posSemidef (htr j) (hfix j)).1
    have hnorm : α.re = ‖α‖ := by
      simpa using congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hnonneg)
    have ha : ‖α‖ ≤ 1 := by rwa [← hnorm]
    refine ⟨ha, ?_⟩
    simp only [h0, correlationLength, norm_zero, Real.log_zero,
      div_zero, Real.exp_zero, mul_one]
    exact (norm_sub_le 1 α).trans (by rw [norm_one]; linarith)
  have hx1 : Real.exp (-γ / correlationLength lam₂) < 1 := by
    rw [neg_div_correlationLength, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg hγ0 (Real.log_neg (norm_pos_iff.mpr h0) hl)
  obtain ⟨K, hK, q₀, hrow⟩ := exists_norm_relativeRow_sub_le hι hdisj hN hA hσ htr hfix
    hl hlam hmix hγ0 hγ hx1
  obtain ⟨Cc, hCc, hdef⟩ := exists_relative_diagonal_deficit_le hι hdisj σ j
    (hσ j).posSemidef (htr j) (hfix j)
  refine ⟨Cc * K ^ 2 + 1, by positivity, q₀, fun μ q hq hq0 => ?_⟩
  obtain ⟨ha, hd⟩ := hdef μ q hq0 (K * Real.exp (-γ / correlationLength lam₂) ^ q)
    (fun k => (hrow μ q hq hq0).2 k j)
  refine ⟨ha, ?_⟩
  have hr : Real.exp (-(2 * γ) * q / correlationLength lam₂) =
      (Real.exp (-γ / correlationLength lam₂) ^ q) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    _ ≤ Cc * (K * Real.exp (-γ / correlationLength lam₂) ^ q) ^ 2 := hd
    _ = (Cc * K ^ 2) * Real.exp (-(2 * γ) * q / correlationLength lam₂) := by
      rw [mul_pow, hr]
      ring
    _ ≤ (Cc * K ^ 2 + 1) * Real.exp (-(2 * γ) * q / correlationLength lam₂) := by
      gcongr
      norm_num

end ActualColumns

end MPSTensor

end
