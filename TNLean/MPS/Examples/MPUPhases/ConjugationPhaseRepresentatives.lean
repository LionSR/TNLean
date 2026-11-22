/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.Phases.ConjugationStrictEquivalence
import TNLean.MPS.MPU.Symmetry.Phases.ConjugationEvenRankEquivalence

/-!
# Invariants of the example gates for the phases under conjugation

Example `ex:all-phases-under-conjugation` of arXiv:1703.09188 (lines 1847--1876) lists gates
realizing every phase under conjugation. With an identification
`e : ℂ^ℓ ⊗ ℂ^r ≅ ℂ^d ⊗ ℂ^d`, let `u_± = v_± ∈ {1, diag(-1, 1, …, 1)}`, and for even `ℓ, r` let
`u'_± = (1_{rℓ/4} ⊗ R) u_±`, `v'_± = v_± (1_{rℓ/4} ⊗ R)` with the matrix `R` of Corollary
`cor:sympl-to-orthogonal`. This file proves the source's verification (lines 1871--1876) for
the tensors in standard form built from these gates:

* each generates a matrix product unitary invariant under conjugation;
* `(u_±, v_±)` are in Case I and `(u'_±, v'_±)` in Case II of Proposition `corconj`;
* `det u_± = det v_± = ±1`, `det (u_+ v_±) = ±1`, and
  `det u'_± = det v'_± = ±(-1)^{rℓ/4}`, using `det R = -1`.

That these labels name distinct strict phases is the "only if" direction of Theorems `conjphs`
and `prop:conjsym-strict-equiv`, which is not used here.

**Local fix (side of `R` on `v'`):** the source prints `v'_± = (1 ⊗ R) v_±`; here `R` acts on the
input of `v'`, as in Corollary `cor:sympl-to-orthogonal`. Documented in
`docs/paper-gaps/mpu_conjugation_example_r_side.tex`.

## Main results

* `MPOTensor.ConjugationExamples.conjugation_caseI_gates`: the Case I representatives.
* `MPOTensor.ConjugationExamples.conjugation_caseII_gates`: the Case II representatives.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

namespace ConjugationExamples

variable {d ℓ r : ℕ}

/-- The diagonal sign flip `diag(-1, 1, …, 1)` of the first coordinate. -/
def signFlip [NeZero d] : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  diagonal fun b ↦ if b = 0 then -1 else 1

/-- The diagonal gate `1` or `diag(-1, 1, …, 1)`, chosen by a sign. -/
def signGate [NeZero d] (s : Bool) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  if s then 1 else signFlip

/-- The sign gates are unitary. -/
theorem signGate_mem_unitaryGroup [NeZero d] (s : Bool) :
    signGate (d := d) s ∈ unitaryGroup (Fin d × Fin d) ℂ := by
  cases s
  · rw [signGate, ite_eq_right (by decide), mem_unitaryGroup_iff, signFlip, star_eq_conjTranspose,
      diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext b
    by_cases h : b = 0 <;> simp [h]
  · simp [signGate]

/-- The sign gates are real. -/
theorem map_star_signGate [NeZero d] (s : Bool) :
    (signGate (d := d) s).map (starRingEnd ℂ) = signGate s := by
  ext i j
  cases s <;> simp only [signGate, signFlip, ite_true, Bool.false_eq_true, ite_false, map_apply,
    diagonal_apply, one_apply] <;> split_ifs <;> simp

/-- The determinant of a sign gate is its sign. -/
theorem det_signGate [NeZero d] (s : Bool) :
    (signGate (d := d) s).det = if s then 1 else -1 := by
  cases s
  · simp only [signGate, signFlip, Bool.false_eq_true, ite_false, det_diagonal]
    rw [Finset.prod_ite_eq' Finset.univ (0 : Fin d × Fin d)]
    simp
  · simp [signGate]

/-- The identification `ℂ^d ⊗ ℂ^d ≅ ℂ^r ⊗ ℂ^ℓ` of the input of the shifted gate. -/
def inputEquiv (e : Fin ℓ × Fin r ≃ Fin d × Fin d) : Fin d × Fin d ≃ Fin r × Fin ℓ :=
  e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r))

/-- The unshifted gate `D : ℂ^d ⊗ ℂ^d → ℂ^ℓ ⊗ ℂ^r` read through `e`. -/
def gateU (e : Fin ℓ × Fin r ≃ Fin d × Fin d) (D : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ :=
  D.submatrix e id

/-- The shifted gate `D : ℂ^r ⊗ ℂ^ℓ → ℂ^d ⊗ ℂ^d` read through `e`. -/
def gateV (e : Fin ℓ × Fin r ≃ Fin d × Fin d) (D : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ :=
  D.submatrix id (inputEquiv e).symm

/-- A unitary matrix read through `e` is a unitary unshifted gate. -/
theorem gateU_isUnitaryBetween (e : Fin ℓ × Fin r ≃ Fin d × Fin d)
    {D : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hD : D ∈ unitaryGroup (Fin d × Fin d) ℂ) :
    (gateU e D).IsUnitaryBetween :=
  ((isUnitaryBetween_iff_mem_unitaryGroup D).mpr hD).reindex D e.symm (Equiv.refl _)

/-- A unitary matrix read through `e` is a unitary shifted gate. -/
theorem gateV_isUnitaryBetween (e : Fin ℓ × Fin r ≃ Fin d × Fin d)
    {D : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hD : D ∈ unitaryGroup (Fin d × Fin d) ℂ) :
    (gateV e D).IsUnitaryBetween :=
  ((isUnitaryBetween_iff_mem_unitaryGroup D).mpr hD).reindex D (Equiv.refl _) (inputEquiv e)

/-- A real matrix gives a real unshifted gate. -/
theorem map_star_gateU (e : Fin ℓ × Fin r ≃ Fin d × Fin d)
    {D : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hD : D.map (starRingEnd ℂ) = D) :
    (gateU e D).map (starRingEnd ℂ) = gateU e D := by
  change (D.map (starRingEnd ℂ)).submatrix e id = _
  rw [hD]
  rfl

/-- A real matrix gives a real shifted gate. -/
theorem map_star_gateV (e : Fin ℓ × Fin r ≃ Fin d × Fin d)
    {D : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hD : D.map (starRingEnd ℂ) = D) :
    (gateV e D).map (starRingEnd ℂ) = gateV e D := by
  change (D.map (starRingEnd ℂ)).submatrix id (inputEquiv e).symm = _
  rw [hD]
  rfl

/-- The determinant of the unshifted gate, read through `e`, is that of the matrix. -/
theorem det_gateU (e : Fin ℓ × Fin r ≃ Fin d × Fin d)
    (D : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((gateU e D).submatrix id e).det = D.det :=
  det_submatrix_equiv_self e D

/-- The determinant of the shifted gate, read through `e`, is that of the matrix. -/
theorem det_gateV (e : Fin ℓ × Fin r ≃ Fin d × Fin d)
    (D : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((gateV e D).submatrix id (inputEquiv e)).det = D.det := by
  rw [gateV, submatrix_submatrix]
  simp

/-- The determinant of `u v`, read through the exchange of the two factors as in Theorem
`conjphs` (arXiv:1703.09188, lines 1406--1416), is the product of the two determinants. -/
theorem det_gateU_mul_gateV (e : Fin ℓ × Fin r ≃ Fin d × Fin d)
    (D₁ D₂ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ((gateU e D₁ * gateV e D₂).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det =
      D₁.det * D₂.det := by
  have h : gateU e D₁ * gateV e D₂ = (D₁ * D₂).submatrix e (inputEquiv e).symm := by
    rw [gateU, gateV, ← submatrix_mul_equiv D₁ D₂ e (Equiv.refl _) (inputEquiv e).symm]
    rfl
  have hf : ((inputEquiv e).symm ∘ Equiv.prodComm (Fin ℓ) (Fin r) : Fin ℓ × Fin r → _) = e := by
    funext a
    simp [inputEquiv]
  rw [h, submatrix_submatrix, hf, Function.comp_id, det_submatrix_equiv_self, det_mul]

/-! ### The symplectic examples -/

private theorem det_symplecticOrthogonalR : symplecticOrthogonalR.det = -1 := by
  set c : ℂ := (1 - Complex.I) / 2
  have h : reindex finProdFinEquiv finProdFinEquiv symplecticOrthogonalR =
      !![c, 0, 0, c * Complex.I; 0, c, -(c * Complex.I), 0; 0, -(c * Complex.I), c, 0;
        c * Complex.I, 0, 0, c] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symplecticOrthogonalR, symplecticY, c, reindex_apply, kroneckerMap_apply,
        finProdFinEquiv, Fin.divNat, Fin.modNat, one_apply]
  rw [← det_reindex_self finProdFinEquiv, h, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, Fin.succAbove]
  simp only [c]
  ring_nf
  norm_num [Complex.I_sq, show Complex.I ^ 4 = 1 by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp]
  ring

private theorem map_star_symplecticOrthogonalR :
    symplecticOrthogonalR.map (starRingEnd ℂ) =
        (symplecticY ⊗ₖ symplecticY) * symplecticOrthogonalR ∧
      symplecticOrthogonalR.map (starRingEnd ℂ) =
        symplecticOrthogonalR * (symplecticY ⊗ₖ symplecticY) := by
  refine ⟨?_, ?_⟩ <;>
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [symplecticOrthogonalR, symplecticY, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
      ring_nf <;> norm_num [Complex.I_sq, Complex.ext_iff]

private theorem symplecticOrthogonalR_mem_unitaryGroup :
    symplecticOrthogonalR ∈ unitaryGroup (Fin 2 × Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
  exact symplecticOrthogonalR_aux.1

/-- The matrix `1_{ℓr/4} ⊗ R` on `ℂ^ℓ ⊗ ℂ^r`, with the two factors `Y` of
`Σ_ℓ ⊗ Σ_r` acting on the factor of `R`. Source: arXiv:1703.09188,
`cor:sympl-to-orthogonal`, lines 1168--1181. -/
noncomputable def regroupedR (hℓ : Even ℓ) (hr : Even r) :
    Matrix (Fin ℓ × Fin r) (Fin ℓ × Fin r) ℂ :=
  reindex (evenPairRegroupEquiv hℓ hr).symm (evenPairRegroupEquiv hℓ hr).symm
    ((1 : Matrix (Fin (ℓ / 2) × Fin (r / 2)) (Fin (ℓ / 2) × Fin (r / 2)) ℂ) ⊗ₖ
      symplecticOrthogonalR)

/-- The matrix `1 ⊗ R` is unitary. -/
theorem regroupedR_mem_unitaryGroup (hℓ : Even ℓ) (hr : Even r) :
    regroupedR hℓ hr ∈ unitaryGroup (Fin ℓ × Fin r) ℂ :=
  reindex_mem_unitaryGroup _ _
    (kronecker_mem_unitary (one_mem _) symplecticOrthogonalR_mem_unitaryGroup)

private theorem reindex_symm_one_kronecker_YY (hℓ : Even ℓ) (hr : Even r) :
    reindex (evenPairRegroupEquiv hℓ hr).symm (evenPairRegroupEquiv hℓ hr).symm
        ((1 : Matrix (Fin (ℓ / 2) × Fin (r / 2)) (Fin (ℓ / 2) × Fin (r / 2)) ℂ) ⊗ₖ
          (symplecticY ⊗ₖ symplecticY)) =
      sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr := by
  rw [← reindex_sourceSkewForm_kronecker hℓ hr]
  simp

/-- Complex conjugation of `1 ⊗ R` multiplies it by `Σ_ℓ ⊗ Σ_r` on either side. -/
theorem map_star_regroupedR (hℓ : Even ℓ) (hr : Even r) :
    (regroupedR hℓ hr).map (starRingEnd ℂ) =
        (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * regroupedR hℓ hr ∧
      (regroupedR hℓ hr).map (starRingEnd ℂ) =
        regroupedR hℓ hr * (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) := by
  have hmap : (regroupedR hℓ hr).map (starRingEnd ℂ) =
      reindex (evenPairRegroupEquiv hℓ hr).symm (evenPairRegroupEquiv hℓ hr).symm
        ((1 : Matrix (Fin (ℓ / 2) × Fin (r / 2)) (Fin (ℓ / 2) × Fin (r / 2)) ℂ) ⊗ₖ
          symplecticOrthogonalR.map (starRingEnd ℂ)) := by
    rw [regroupedR]
    change reindex _ _ (((1 : Matrix (Fin (ℓ / 2) × Fin (r / 2)) _ ℂ) ⊗ₖ
      symplecticOrthogonalR).map (starRingEnd ℂ)) = _
    rw [map_star_kronecker, Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)]
  obtain ⟨h₁, h₂⟩ := map_star_symplecticOrthogonalR
  refine ⟨?_, ?_⟩
  · rw [hmap, h₁, ← reindex_symm_one_kronecker_YY hℓ hr, regroupedR, ← one_mul (1 : Matrix _ _ ℂ),
      mul_kronecker_mul, one_mul]
    simp only [reindex_apply, submatrix_mul_equiv]
  · rw [hmap, h₂, ← reindex_symm_one_kronecker_YY hℓ hr, regroupedR, ← one_mul (1 : Matrix _ _ ℂ),
      mul_kronecker_mul, one_mul]
    simp only [reindex_apply, submatrix_mul_equiv]

/-- `det (1_{rℓ/4} ⊗ R) = (-1)^{rℓ/4}`, from `det R = -1`; arXiv:1703.09188, lines 1874--1876. -/
theorem det_regroupedR (hℓ : Even ℓ) (hr : Even r) :
    (regroupedR hℓ hr).det = (-1) ^ ((ℓ / 2) * (r / 2)) := by
  rw [regroupedR, det_reindex_self, det_kronecker, det_one, one_pow, one_mul,
    det_symplecticOrthogonalR]
  simp

private theorem conjTranspose_kronecker_sourceSkewForm (hℓ : Even ℓ) (hr : Even r) :
    (sourceSkewForm hr)ᴴ ⊗ₖ (sourceSkewForm hℓ)ᴴ = sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ := by
  have h : ∀ {n : ℕ} (hn : Even n), (sourceSkewForm hn)ᴴ = -sourceSkewForm hn := fun hn ↦ by
    rw [conjTranspose, transpose_sourceSkewForm]
    ext i j
    have := congrFun (congrFun (map_star_sourceSkewForm hn) i) j
    simpa using this
  rw [h hr, h hℓ]
  ext i j
  simp [kroneckerMap_apply]

/-! ### The example gates -/

/-- The sign `1` or `-1` of a Boolean choice. -/
def boolSign (s : Bool) : ℂ := if s then 1 else -1

section Gates

variable [NeZero d] [NeZero ℓ] [NeZero r] (e : Fin ℓ × Fin r ≃ Fin d × Fin d)

/-- **Case I representatives.** For the gates `u = D₁`, `v = D₂` with
`D_i ∈ {1, diag(-1, 1, …, 1)}` read through `e`, the matrix product unitary of
the tensor in standard form is invariant under conjugation, the gates are in
Case I, and their determinants are the chosen signs.

Source: arXiv:1703.09188, Example `ex:all-phases-under-conjugation`, item 1,
lines 1851--1862, with the verification at lines 1871--1876. -/
theorem conjugation_caseI_gates (s₁ s₂ : Bool) :
    IsInvariantUnderSymmetry (conjugationSymmetry (d * d))
        (reindexPhysical (Equiv.refl _)
          (standardFormTensorOfGates (gateU e (signGate s₁)) (gateV e (signGate s₂)))) ∧
      IsConjugationCaseI (gateU e (signGate s₁)) (gateV e (signGate s₂)) ∧
      ((gateU e (signGate s₁)).submatrix id e).det = boolSign s₁ ∧
      ((gateV e (signGate s₂)).submatrix id (inputEquiv e)).det = boolSign s₂ ∧
      ((gateU e (signGate s₁) * gateV e (signGate s₂)).submatrix id
        (Equiv.prodComm (Fin ℓ) (Fin r))).det = boolSign s₁ * boolSign s₂ := by
  have hu := map_star_gateU e (map_star_signGate (d := d) s₁)
  have hv := map_star_gateV e (map_star_signGate (d := d) s₂)
  refine ⟨?_, ⟨1, 1, one_mem _, one_mem _, transpose_one, transpose_one, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine isInvariantUnderSymmetry_conjugation_standardFormTensorOfGates (Equiv.refl _)
      (gateU_isUnitaryBetween e (signGate_mem_unitaryGroup s₁))
      (gateV_isUnitaryBetween e (signGate_mem_unitaryGroup s₂)) 1 1 ?_ ?_
    · simp [hu]
    · simp [hv]
  · simp [hu]
  · simp [hv]
  · rw [det_gateU, det_signGate, boolSign]
  · rw [det_gateV, det_signGate, boolSign]
  · rw [det_gateU_mul_gateV, det_signGate, det_signGate, boolSign, boolSign]

/-- **Case II representatives.** For even ranks and the gates
`u' = (1_{rℓ/4} ⊗ R) D₁`, `v' = D₂ (1_{rℓ/4} ⊗ R)` with
`D_i ∈ {1, diag(-1, 1, …, 1)}` read through `e`, the matrix product unitary of
the tensor in standard form is invariant under conjugation, the gates are in
Case II, and `det u' = (-1)^{rℓ/4} det D₁`, `det v' = (-1)^{rℓ/4} det D₂`.
The side of `R` on `v'` follows Corollary `cor:sympl-to-orthogonal` (module docstring).

Source: arXiv:1703.09188, Example `ex:all-phases-under-conjugation`, item 2,
lines 1863--1869, with the verification at lines 1871--1876. -/
theorem conjugation_caseII_gates (hℓ : Even ℓ) (hr : Even r) (s₁ s₂ : Bool) :
    IsInvariantUnderSymmetry (conjugationSymmetry (d * d))
        (reindexPhysical (Equiv.refl _)
          (standardFormTensorOfGates (regroupedR hℓ hr * gateU e (signGate s₁))
            (gateV e (signGate s₂) * regroupedR hr hℓ))) ∧
      IsConjugationCaseII (regroupedR hℓ hr * gateU e (signGate s₁))
        (gateV e (signGate s₂) * regroupedR hr hℓ) ∧
      ((regroupedR hℓ hr * gateU e (signGate s₁)).submatrix id e).det =
        (-1) ^ ((ℓ / 2) * (r / 2)) * boolSign s₁ ∧
      ((gateV e (signGate s₂) * regroupedR hr hℓ).submatrix id (inputEquiv e)).det =
        (-1) ^ ((r / 2) * (ℓ / 2)) * boolSign s₂ := by
  have hu := map_star_gateU e (map_star_signGate (d := d) s₁)
  have hv := map_star_gateV e (map_star_signGate (d := d) s₂)
  have hcu : (regroupedR hℓ hr * gateU e (signGate s₁)).map (starRingEnd ℂ) =
      (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * (regroupedR hℓ hr * gateU e (signGate s₁)) := by
    rw [Matrix.map_mul, (map_star_regroupedR hℓ hr).1, hu, Matrix.mul_assoc]
  have hcv : (gateV e (signGate s₂) * regroupedR hr hℓ).map (starRingEnd ℂ) =
      (gateV e (signGate s₂) * regroupedR hr hℓ) *
        ((sourceSkewForm hr)ᴴ ⊗ₖ (sourceSkewForm hℓ)ᴴ) := by
    rw [Matrix.map_mul, (map_star_regroupedR hr hℓ).2, hv, Matrix.mul_assoc,
      conjTranspose_kronecker_sourceSkewForm hℓ hr]
  refine ⟨?_, ⟨sourceSkewForm hℓ, sourceSkewForm hr, sourceSkewForm_mem_unitaryGroup hℓ,
    sourceSkewForm_mem_unitaryGroup hr, transpose_sourceSkewForm hℓ, transpose_sourceSkewForm hr,
    hcu, hcv⟩, ?_, ?_⟩
  · exact isInvariantUnderSymmetry_conjugation_standardFormTensorOfGates (Equiv.refl _)
      (((isUnitaryBetween_iff_mem_unitaryGroup _).mpr (regroupedR_mem_unitaryGroup hℓ hr)).mul _ _
        (gateU_isUnitaryBetween e (signGate_mem_unitaryGroup s₁)))
      ((gateV_isUnitaryBetween e (signGate_mem_unitaryGroup s₂)).mul _ _
        ((isUnitaryBetween_iff_mem_unitaryGroup _).mpr (regroupedR_mem_unitaryGroup hr hℓ)))
      ⟨_, sourceSkewForm_mem_unitaryGroup hℓ⟩ ⟨_, sourceSkewForm_mem_unitaryGroup hr⟩ hcu hcv
  · have h : (regroupedR hℓ hr * gateU e (signGate s₁)).submatrix id e =
        regroupedR hℓ hr * (gateU e (signGate s₁)).submatrix id e := rfl
    rw [h, det_mul, det_gateU, det_signGate, det_regroupedR, boolSign]
  · have h : (gateV e (signGate s₂) * regroupedR hr hℓ).submatrix id (inputEquiv e) =
        (gateV e (signGate s₂)).submatrix id (inputEquiv e) *
          (regroupedR hr hℓ).submatrix (inputEquiv e) (inputEquiv e) :=
      (submatrix_mul_equiv _ _ _ _ _).symm
    rw [h, det_mul, det_gateV, det_submatrix_equiv_self, det_signGate, det_regroupedR, boolSign,
      mul_comm]

end Gates

end ConjugationExamples

end MPOTensor
