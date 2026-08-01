/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.SitewisePhysicalMatrix
import TNLean.MPS.MPDO.VerticalProductPairBlocks

/-!
# Positivity forced by a tensor-attached BNT algebra clause

The positive one-site MPO restricts to every retained vertical BNT copy.  Since
its multiplicity weight is strictly positive, the terminal physical-trace
transfer of the corresponding normal tensor is positive semidefinite.

This conclusion uses only the vertical canonical-form fields of
`BNTAlgebraTensorClause`; no fusion data or marked-chain realization is needed.
-/

open scoped Matrix BigOperators ComplexOrder

noncomputable section

namespace MPOTensor.BNTAlgebraTensorClause

open MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {M : MPOTensor d D}

private abbrev retainedDim (H : BNTAlgebraTensorClause M) : ℕ :=
  ∑ q : Fin (∑ α : Fin H.labelCount, H.multiplicity α),
    verticalCopyDim H.bondDim H.multiplicity q

private def retainedAssembledMPO (H : BNTAlgebraTensorClause M) :
    MPOTensor H.retainedDim D :=
  fun i j a b ↦ verticalAssembledTensor H.bondDim H.multiplicity H.weight H.tensor
    (finProdFinEquiv (a, b)) i j

private theorem changePhysicalBasis_verticalCoisometry_eq_retainedAssembledMPO
    (H : BNTAlgebraTensorClause M) :
    changePhysicalBasis H.verticalCoisometry M = H.retainedAssembledMPO := by
  ext i j a b
  unfold changePhysicalBasis retainedAssembledMPO
  have hs : physicalSlice M a b = verticalTensor M (finProdFinEquiv (a, b)) := by
    ext s t
    simp [physicalSlice]
  rw [hs, H.forward]

private def verticalCopyLetter (H : BNTAlgebraTensorClause M)
    (p : (α : Fin H.labelCount) × Fin (H.multiplicity α))
    (x y : Fin (H.bondDim p.1)) : Matrix (Fin D) (Fin D) ℂ :=
  fun a b ↦ H.tensor p.1 (finProdFinEquiv (a, b)) x y

private theorem changePhysicalBasis_verticalCoisometry_copy_same
    (H : BNTAlgebraTensorClause M)
    (p : (α : Fin H.labelCount) × Fin (H.multiplicity α))
    (x y : Fin (H.bondDim p.1)) :
    changePhysicalBasis H.verticalCoisometry M
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, x⟩)
        ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, y⟩) =
      H.weight p.1 p.2 • H.verticalCopyLetter p x y := by
  rw [H.changePhysicalBasis_verticalCoisometry_eq_retainedAssembledMPO]
  ext a b
  have hAssembled := congrFun (congrFun
    (verticalAssembledTensor_reindex_copyCoordinates H.bondDim H.multiplicity
      H.weight H.tensor (finProdFinEquiv (a, b)))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, x⟩))
    ((verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, y⟩)
  simpa only [retainedAssembledMPO, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply, Matrix.blockDiagonal'_apply_eq,
    Matrix.smul_apply, verticalCopyLetter] using hAssembled

/-- Every retained vertical BNT tensor in a tensor-attached algebra clause has
positive-semidefinite terminal physical-trace transfer.

The result is a necessary one-site consequence of the clause and MPDO
positivity.  In particular, a proposed normal representative whose terminal
transfer is not positive semidefinite cannot occur as one of these retained
sectors.

Source: arXiv:1606.00608, Proposition 4.13, lines 943--951, and the terminal
matrices at lines 1010--1012. -/
theorem physTraceTransfer_verticalBNTMPO_posSemidef
    (H : BNTAlgebraTensorClause M) (hM : IsMPDO M) (γ : Fin H.labelCount) :
    (physTraceTransfer (verticalBNTMPO (H.tensor γ))).PosSemidef := by
  classical
  let q : Fin (H.multiplicity γ) := ⟨0, H.multiplicity_pos γ⟩
  let p : (α : Fin H.labelCount) × Fin (H.multiplicity α) := ⟨γ, q⟩
  let e : Fin (H.bondDim γ) → (Fin 1 → Fin H.retainedDim) :=
    fun x _ ↦
      (verticalCopyCoordinateEquiv H.bondDim H.multiplicity).symm ⟨p, x⟩
  have hRetained :
      (mpo (changePhysicalBasis H.verticalCoisometry M) 1).PosSemidef := by
    rw [← singleKrausMap_sitewisePhysicalMatrix_mpo]
    exact (singleKrausMap_isKrausCP _).map_posSemidef (hM 1 zero_lt_one)
  have hPrincipalEq :
      (mpo (changePhysicalBasis H.verticalCoisometry M) 1).submatrix e e =
        H.weight γ q • physTraceTransfer (verticalBNTMPO (H.tensor γ)) := by
    ext x y
    simp only [Matrix.submatrix_apply, mpo_apply, mpoMatrixEntry, List.ofFn_succ,
      List.ofFn_zero, evalWord_cons, evalWord_nil, Matrix.mul_one, e]
    rw [H.changePhysicalBasis_verticalCoisometry_copy_same]
    rw [Matrix.trace_smul, Matrix.smul_apply]
    congr 1
    simp [p, Matrix.trace, physTraceTransfer, Matrix.sum_apply, verticalCopyLetter,
      verticalBNTMPO]
  have hScaled :
      (H.weight γ q • physTraceTransfer (verticalBNTMPO (H.tensor γ))).PosSemidef := by
    rw [← hPrincipalEq]
    exact hRetained.submatrix e
  have hUnscaled :
      ((H.weight γ q)⁻¹ •
        (H.weight γ q • physTraceTransfer (verticalBNTMPO (H.tensor γ)))).PosSemidef :=
    hScaled.smul (inv_nonneg_of_nonneg (H.weight_pos γ q).le)
  simpa only [inv_smul_smul₀ (H.weight_pos γ q).ne'] using hUnscaled

end MPOTensor.BNTAlgebraTensorClause
