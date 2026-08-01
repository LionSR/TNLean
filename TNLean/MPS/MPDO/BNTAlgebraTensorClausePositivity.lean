/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTAlgebraTensorClause
import TNLean.MPS.MPDO.SitewisePhysicalMatrix
import TNLean.MPS.MPDO.VerticalSectorCoordinates

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

private theorem verticalAssembledTensor_apply_copy_same
    (H : BNTAlgebraTensorClause M) (γ : Fin H.labelCount)
    (q : Fin (H.multiplicity γ)) (v : Fin (D * D))
    (x y : Fin (H.bondDim γ)) :
    verticalAssembledTensor H.bondDim H.multiplicity H.weight H.tensor v
        (verticalSectorFinEquiv H.bondDim H.multiplicity ⟨γ, (q, x)⟩)
        (verticalSectorFinEquiv H.bondDim H.multiplicity ⟨γ, (q, y)⟩) =
      H.weight γ q * H.tensor γ v x y := by
  unfold verticalAssembledTensor MPSTensor.toTensorFromBlocks
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    verticalSectorFinEquiv_outer_symm]
  rw [Matrix.blockDiagonal'_apply_eq]
  let p := finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨γ, q⟩)
  have hp : p = ⟨γ, q⟩ := finSigmaFinEquiv.symm_apply_apply ⟨γ, q⟩
  have hdim : H.bondDim p.1 = H.bondDim γ :=
    congrArg (fun s ↦ H.bondDim s.1) hp
  have hweight : H.weight p.1 p.2 = H.weight γ q :=
    congrArg (fun s ↦ H.weight s.1 s.2) hp
  let block (s : (α : Fin H.labelCount) × Fin (H.multiplicity α)) :=
    H.tensor s.1 v
  let packed (s : (α : Fin H.labelCount) × Fin (H.multiplicity α)) :
      (r : (α : Fin H.labelCount) × Fin (H.multiplicity α)) ×
        Matrix (Fin (H.bondDim r.1)) (Fin (H.bondDim r.1)) ℂ :=
    ⟨s, block s⟩
  have hpacked : packed p = packed ⟨γ, q⟩ := congrArg packed hp
  have hblock : HEq (block p) (block ⟨γ, q⟩) :=
    (Sigma.mk.inj_iff.mp hpacked).2
  have hentry := (Fin.heq_fun₂_iff hdim.symm hdim.symm).mp hblock.symm x y
  simp only [verticalCopyWeights, verticalCopyBlocks]
  change H.weight p.1 p.2 * block p (Fin.cast _ x) (Fin.cast _ y) = _
  rw [hweight]
  exact congrArg (H.weight γ q * ·) hentry.symm

private theorem changePhysicalBasis_verticalCoisometry_copy_same
    (H : BNTAlgebraTensorClause M) (γ : Fin H.labelCount)
    (q : Fin (H.multiplicity γ)) (x y : Fin (H.bondDim γ)) :
    changePhysicalBasis H.verticalCoisometry M
        (verticalSectorFinEquiv H.bondDim H.multiplicity ⟨γ, (q, x)⟩)
        (verticalSectorFinEquiv H.bondDim H.multiplicity ⟨γ, (q, y)⟩) =
      H.weight γ q • H.verticalCopyLetter ⟨γ, q⟩ x y := by
  rw [H.changePhysicalBasis_verticalCoisometry_eq_retainedAssembledMPO]
  ext a b
  exact H.verticalAssembledTensor_apply_copy_same γ q (finProdFinEquiv (a, b)) x y

/-- Every retained vertical BNT tensor in a tensor-attached algebra clause has
positive-semidefinite terminal physical-trace transfer.

The result is a necessary one-site consequence of the clause and MPDO
positivity.  In particular, a proposed normal representative whose terminal
transfer is not positive semidefinite cannot occur as one of these retained
sectors.

Derived from arXiv:1606.00608, Proposition 4.13, and one-site MPDO
positivity; compare the terminal matrices at lines 1010--1012. -/
theorem physTraceTransfer_verticalBNTMPO_posSemidef
    (H : BNTAlgebraTensorClause M) (hM : IsMPDO M) (γ : Fin H.labelCount) :
    (physTraceTransfer (verticalBNTMPO (H.tensor γ))).PosSemidef := by
  classical
  let q : Fin (H.multiplicity γ) := ⟨0, H.multiplicity_pos γ⟩
  let e : Fin (H.bondDim γ) → (Fin 1 → Fin H.retainedDim) :=
    fun x _ ↦ verticalSectorFinEquiv H.bondDim H.multiplicity ⟨γ, (q, x)⟩
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
    rw [H.changePhysicalBasis_verticalCoisometry_copy_same γ q]
    rw [Matrix.trace_smul, Matrix.smul_apply]
    congr 1
    simp [Matrix.trace, physTraceTransfer, Matrix.sum_apply, verticalCopyLetter,
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
