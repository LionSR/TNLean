/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.Defs
import TNLean.MPS.MPDO.ZCL
import TNLean.MPS.RFP.Defs

/-!
# Purification RFP for LPDO tensors

This file packages the local purification data used by `MPOTensor.IsLPDO` and
defines the mixed-state purification RFP condition from arXiv:1606.00608,
Definition 4.3.

## Main definitions

* `MPOTensor.IsLPDOWitness`: a packaged LPDO witness for a fixed purifying
  tensor family and bond-space equivalence.
* `MPOTensor.purifyingMPSTensor`: the doubled-index MPS tensor associated to
  a purifying family `A`.
* `MPOTensor.IsPRFP`: an MPO tensor admits an LPDO witness whose purifying MPS
  tensor is a pure-state RFP.
* `MPOTensor.exists_isPRFP_not_isZCL`: a concrete counterexample showing that
  the current `IsPRFP` definition does not imply MPO ZCL.
* `MPOTensor.isPRFP_not_implies_isZCL`: the corresponding global negation of
  the implication `IsPRFP M → IsZCL M`.

## References

* [CPGSV17] arXiv:1606.00608, §4.3
-/

open scoped Matrix BigOperators Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- A packaged witness for the LPDO relation of `M` with a fixed purifying
family `A` and bond-space identification `e`. This isolates the witness data
from `IsLPDO` so it can be reused in purification-RFP statements. -/
def IsLPDOWitness {dK D' : ℕ} (M : MPOTensor d D)
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D') : Prop :=
  ∀ i j : Fin d, M i j = (∑ k : Fin dK,
    (A i k) ⊗ₖ ((A j k).map (starRingEnd ℂ))).submatrix ↑e ↑e

/-- The MPS tensor obtained by bundling the physical and ancilla indices of a
purifying family `A`. -/
def purifyingMPSTensor {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) : MPSTensor (d * dK) D' :=
  fun ik => A ik.divNat ik.modNat

@[simp] lemma purifyingMPSTensor_apply {dK D' : ℕ}
    (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ) (ik : Fin (d * dK)) :
    purifyingMPSTensor A ik = A ik.divNat ik.modNat :=
  rfl

/-- Repackaging `IsLPDO` in terms of `IsLPDOWitness`. -/
theorem isLPDO_iff_exists_witness (M : MPOTensor d D) :
    IsLPDO M ↔
      ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
        (e : Fin D ≃ Fin D' × Fin D'),
        IsLPDOWitness M A e :=
  Iff.rfl

/-- An LPDO has a **purification RFP** when it admits a local purification
whose purifying MPS tensor is a pure-state RFP.

See arXiv:1606.00608, Definition 4.3. -/
def IsPRFP (M : MPOTensor d D) : Prop :=
  ∃ (dK D' : ℕ) (A : Fin d → Fin dK → Matrix (Fin D') (Fin D') ℂ)
    (e : Fin D ≃ Fin D' × Fin D'),
    IsLPDOWitness M A e ∧ MPSTensor.IsRFP (purifyingMPSTensor A)

/-- A purification-RFP tensor is, in particular, an LPDO. -/
theorem IsPRFP.isLPDO {M : MPOTensor d D} (h : IsPRFP M) : IsLPDO M := by
  rcases h with ⟨dK, D', A, e, hWitness, _hRFP⟩
  exact ⟨dK, D', A, e, hWitness⟩

section Counterexample

private noncomputable def scalarMat (z : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => z

private noncomputable def prfpCounterexamplePurifyingTensor : MPSTensor 4 1
  | ⟨0, _⟩ => scalarMat (3 / 5 : ℂ)
  | ⟨1, _⟩ => scalarMat 0
  | ⟨2, _⟩ => scalarMat 0
  | ⟨3, _⟩ => scalarMat (4 / 5 : ℂ)

private noncomputable def prfpCounterexamplePurifyingFamily :
    Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℂ
  | ⟨0, _⟩, ⟨0, _⟩ => scalarMat (3 / 5 : ℂ)
  | ⟨0, _⟩, ⟨1, _⟩ => scalarMat 0
  | ⟨1, _⟩, ⟨0, _⟩ => scalarMat 0
  | ⟨1, _⟩, ⟨1, _⟩ => scalarMat (4 / 5 : ℂ)

private noncomputable def prfpCounterexamplePurifyingFamilyEquiv :
    Fin 2 → Fin 2 → Matrix (Fin 1) (Fin 1) ℂ :=
  fun i k => prfpCounterexamplePurifyingTensor (finProdFinEquiv (i, k))

private noncomputable def prfpCounterexampleBondEquiv : Fin 1 ≃ Fin 1 × Fin 1 where
  toFun _ := (0, 0)
  invFun _ := 0
  left_inv := by intro x; fin_cases x; rfl
  right_inv := by rintro ⟨a, b⟩; fin_cases a; fin_cases b; rfl

private noncomputable def prfpCounterexampleTensor : MPOTensor 2 1 :=
  fun i j => (∑ k : Fin 2,
    (prfpCounterexamplePurifyingFamily i k) ⊗ₖ
      ((prfpCounterexamplePurifyingFamily j k).map (starRingEnd ℂ))).submatrix
        ↑prfpCounterexampleBondEquiv ↑prfpCounterexampleBondEquiv

private noncomputable def prfpCounterexampleBundledTensor : MPSTensor 4 1
  | ⟨0, _⟩ => scalarMat (9 / 25 : ℂ)
  | ⟨1, _⟩ => scalarMat 0
  | ⟨2, _⟩ => scalarMat 0
  | ⟨3, _⟩ => scalarMat (16 / 25 : ℂ)

private noncomputable def prfpCounterexampleBundledMPO : MPOTensor 2 1 :=
  fun i j => prfpCounterexampleBundledTensor (finProdFinEquiv (i, j))

private lemma prfpCounterexamplePurifyingFamily_eq_equiv :
    prfpCounterexamplePurifyingFamily = prfpCounterexamplePurifyingFamilyEquiv := by
  ext i k x y
  fin_cases i <;> fin_cases k <;> fin_cases x <;> fin_cases y
  all_goals
    norm_num [prfpCounterexamplePurifyingFamily, prfpCounterexamplePurifyingFamilyEquiv,
      prfpCounterexamplePurifyingTensor, scalarMat, finProdFinEquiv]

private lemma prfpCounterexample_purifyingMPSTensor_eq :
    purifyingMPSTensor prfpCounterexamplePurifyingFamily =
      prfpCounterexamplePurifyingTensor := by
  rw [prfpCounterexamplePurifyingFamily_eq_equiv]
  funext x
  change prfpCounterexamplePurifyingTensor (finProdFinEquiv (x.divNat, x.modNat)) =
    prfpCounterexamplePurifyingTensor x
  exact congrArg prfpCounterexamplePurifyingTensor (finProdFinEquiv.apply_symm_apply x)

private lemma prfpCounterexamplePurifyingTensor_isRFP :
    MPSTensor.IsRFP prfpCounterexamplePurifyingTensor := by
  ext X i j
  fin_cases i
  fin_cases j
  simp [MPSTensor.transferMap_apply, prfpCounterexamplePurifyingTensor,
    scalarMat, Fin.sum_univ_four, Matrix.mul_apply]
  ring_nf

private lemma prfpCounterexampleTensor_eq_bundled :
    prfpCounterexampleTensor = prfpCounterexampleBundledMPO := by
  ext i j x y
  fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y
  · have h3 : (starRingEnd ℂ) (3 : ℂ) = (3 : ℂ) := by
      simpa using Complex.conj_ofReal (3 : ℝ)
    have h5 : (starRingEnd ℂ) (5 : ℂ) = (5 : ℂ) := by
      simpa using Complex.conj_ofReal (5 : ℝ)
    norm_num [prfpCounterexampleTensor, prfpCounterexampleBundledMPO,
      prfpCounterexamplePurifyingFamily, prfpCounterexampleBundledTensor,
      prfpCounterexampleBondEquiv, scalarMat, Matrix.kroneckerMap_apply,
      Fin.sum_univ_two, finProdFinEquiv, h3, h5]
  · norm_num [prfpCounterexampleTensor, prfpCounterexampleBundledMPO,
      prfpCounterexamplePurifyingFamily, prfpCounterexampleBundledTensor,
      prfpCounterexampleBondEquiv, scalarMat, Matrix.kroneckerMap_apply,
      Fin.sum_univ_two, finProdFinEquiv]
  · norm_num [prfpCounterexampleTensor, prfpCounterexampleBundledMPO,
      prfpCounterexamplePurifyingFamily, prfpCounterexampleBundledTensor,
      prfpCounterexampleBondEquiv, scalarMat, Matrix.kroneckerMap_apply,
      Fin.sum_univ_two, finProdFinEquiv]
  · have h4 : (starRingEnd ℂ) (4 : ℂ) = (4 : ℂ) := by
      simpa using Complex.conj_ofReal (4 : ℝ)
    have h5 : (starRingEnd ℂ) (5 : ℂ) = (5 : ℂ) := by
      simpa using Complex.conj_ofReal (5 : ℝ)
    norm_num [prfpCounterexampleTensor, prfpCounterexampleBundledMPO,
      prfpCounterexamplePurifyingFamily, prfpCounterexampleBundledTensor,
      prfpCounterexampleBondEquiv, scalarMat, Matrix.kroneckerMap_apply,
      Fin.sum_univ_two, finProdFinEquiv, h4, h5]

private lemma prfpCounterexampleBundledMPO_toMPSTensor_eq :
    prfpCounterexampleBundledMPO.toMPSTensor = prfpCounterexampleBundledTensor := by
  funext x
  change prfpCounterexampleBundledTensor (finProdFinEquiv (x.divNat, x.modNat)) =
    prfpCounterexampleBundledTensor x
  exact congrArg prfpCounterexampleBundledTensor (finProdFinEquiv.apply_symm_apply x)

private lemma prfpCounterexampleBundledTensor_not_isRFP :
    ¬ MPSTensor.IsRFP prfpCounterexampleBundledTensor := by
  intro hRFP
  have h := congr_fun (congr_arg DFunLike.coe hRFP) (1 : Matrix (Fin 1) (Fin 1) ℂ)
  have h00 := congr_fun (congr_fun h 0) 0
  simp [MPSTensor.transferMap_apply, prfpCounterexampleBundledTensor,
    scalarMat, Fin.sum_univ_four, Matrix.mul_apply] at h00
  norm_num at h00

private lemma prfpCounterexampleBundledMPO_not_isZCL :
    ¬ IsZCL prfpCounterexampleBundledMPO := by
  intro hZCL
  have hRFP : MPSTensor.IsRFP prfpCounterexampleBundledMPO.toMPSTensor :=
    (isZCL_iff_toMPSTensor_isRFP prfpCounterexampleBundledMPO).1 hZCL
  exact prfpCounterexampleBundledTensor_not_isRFP (by
    simpa [prfpCounterexampleBundledMPO_toMPSTensor_eq] using hRFP)

/-- A concrete counterexample showing that the current `IsPRFP` definition does
not imply MPO zero correlation length. The witness already appears for bond
dimension `1`, with purifying coefficients `3/5` and `4/5`. -/
theorem exists_isPRFP_not_isZCL : ∃ M : MPOTensor 2 1, IsPRFP M ∧ ¬ IsZCL M := by
  refine ⟨prfpCounterexampleTensor, ?_, ?_⟩
  · refine ⟨2, 1, prfpCounterexamplePurifyingFamily, prfpCounterexampleBondEquiv, ?_, ?_⟩
    · intro i j
      rfl
    · simpa [prfpCounterexample_purifyingMPSTensor_eq] using
        prfpCounterexamplePurifyingTensor_isRFP
  · intro hZCL
    have hZCL' : IsZCL prfpCounterexampleBundledMPO := by
      simpa [prfpCounterexampleTensor_eq_bundled] using hZCL
    exact prfpCounterexampleBundledMPO_not_isZCL hZCL'

/-- Consequently, the implication `IsPRFP M → IsZCL M` is false for the current
definition of `IsPRFP`. -/
theorem isPRFP_not_implies_isZCL :
    ¬ ∀ {d D : ℕ} {M : MPOTensor d D}, IsPRFP M → IsZCL M := by
  intro h
  rcases exists_isPRFP_not_isZCL with ⟨M, hPRFP, hNotZCL⟩
  exact hNotZCL (h hPRFP)

end Counterexample

/-!
### Future work

The naive implication `IsPRFP.isZCL` is **false** for the current definition of
`IsPRFP`; see `exists_isPRFP_not_isZCL` and `isPRFP_not_implies_isZCL`. Any
future mixed-state theorem of this form will need extra hypotheses or a
strengthened notion of PRFP that keeps track of the additional mixed-state
structure.
-/

end MPOTensor
