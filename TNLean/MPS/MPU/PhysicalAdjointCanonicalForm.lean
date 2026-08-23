/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Conjugation
import TNLean.MPS.MPU.CanonicalForm
import TNLean.MPS.MPDO.PhysicalAdjoint

/-!
# Reduced canonical-form-II data under physical adjunction

Physical adjunction of an MPO exchanges its two physical coordinates and conjugates every
coefficient. This file transports literal CPSV canonical-form-II data through that operation.
The construction preserves canonical form II unconditionally and preserves the reduced
full-active-support condition when it holds for the original data.

## Main definitions

* `MPOTensor.physicalPairSwapEquiv`: exchange of the two flattened physical coordinates.
* `MPSTensor.CPSVCanonicalFormIIData.physicalAdjointNormalizedFlattening`: transformed CFII data.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, Appendix A,
  lines 1054--1077, for the literal canonical-form-II structure.
* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1703.09188, equation `Erightleft`,
  lines 271--281, and equation `eq:transfer-op`, lines 336--340, for the MPU normalization context.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Exchange the two coordinates of a flattened physical pair.

This is the existing pair-swap equivalence, named here for its role on the physical alphabet rather
than its role on a doubled virtual bond. -/
def physicalPairSwapEquiv (d : ℕ) : Fin (d * d) ≃ Fin (d * d) :=
  bondPairSwapEquiv d

/-- The physical-pair swap exchanges the two coordinates under `finProdFinEquiv`. -/
@[simp] theorem physicalPairSwapEquiv_finProdFinEquiv (i j : Fin d) :
    physicalPairSwapEquiv d (finProdFinEquiv (i, j)) = finProdFinEquiv (j, i) := by
  rw [physicalPairSwapEquiv, bondPairSwapEquiv_apply, bondPairSwap_finProdFinEquiv]

/-- The physical-pair swap is its own inverse. -/
@[simp] theorem physicalPairSwapEquiv_symm :
    (physicalPairSwapEquiv d).symm = physicalPairSwapEquiv d := by
  rw [physicalPairSwapEquiv, bondPairSwapEquiv_symm]

/-- The normalized flattening of the physical adjoint is obtained by applying entrywise complex
conjugation to every virtual matrix entry and exchanging the two flattened physical coordinates. -/
theorem normalizedFlattening_physicalAdjointTensor (U : MPOTensor d D) :
    (physicalAdjointTensor U).normalizedFlattening =
      Kraus.reindexPhysical (physicalPairSwapEquiv d)
        (MPSTensor.mapStar U.normalizedFlattening) := by
  ext ij β α
  rw [show ij = finProdFinEquiv (ij.divNat, ij.modNat) by
    exact (finProdFinEquiv.apply_symm_apply ij).symm]
  simp [normalizedFlattening, Kraus.reindexPhysical, MPSTensor.mapStar,
    MPOTensor.toMPSTensor, Matrix.smul_apply, Matrix.map_apply, RCLike.star_def]

end MPOTensor

namespace MPSTensor.CPSVCanonicalFormIIData

variable {d D : ℕ} {U : MPOTensor d D}

/-- Transport literal CPSV canonical-form-II data through physical adjunction.

The block count and dimensions are unchanged. We conjugate the weights, blocks, and ambient
coisometry entrywise, then exchange the two physical coordinates. A diagonal positive-definite
fixed point is real, so the same matrix remains fixed by the transformed transfer map.

The literal canonical-form-II structure is from arXiv:1606.00608, Appendix A,
lines 1054--1077. The normalization equations used here are the MPU context in
arXiv:1703.09188, equation `Erightleft`, lines 271--281, and equation `eq:transfer-op`,
lines 336--340. -/
noncomputable def physicalAdjointNormalizedFlattening
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) :
    CPSVCanonicalFormIIData (MPOTensor.physicalAdjointTensor U).normalizedFlattening where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := fun k ↦ star (data.weights k)
  weights_ne_zero := fun k ↦ star_ne_zero.mpr (data.weights_ne_zero k)
  blocks := fun k ↦ Kraus.reindexPhysical (MPOTensor.physicalPairSwapEquiv d)
    (MPSTensor.mapStar (data.blocks k))
  blocks_normal := fun k ↦
    (MPSTensor.IsNormalTensor.mapStar (data.blocks_normal k)).reindexPhysical
      (MPOTensor.physicalPairSwapEquiv d)
  total_dim_le := data.total_dim_le
  ambient_coisometry := data.ambient_coisometry.map (starRingEnd ℂ)
  coisometric := by
    have hmap := congrArg (fun M ↦ M.map (starRingEnd ℂ)) data.coisometric
    simpa [Matrix.map_mul,
      Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])] using hmap
  reconstruct := by
    intro i
    rw [MPOTensor.normalizedFlattening_physicalAdjointTensor]
    have hmap := congrArg (fun M ↦ M.map (starRingEnd ℂ))
      (data.reconstruct (MPOTensor.physicalPairSwapEquiv d i))
    have hmiddle :
        (MPSTensor.toTensorFromBlocks data.weights data.blocks
          (MPOTensor.physicalPairSwapEquiv d i)).map (starRingEnd ℂ) =
          MPSTensor.toTensorFromBlocks (fun k ↦ star (data.weights k))
            (fun k ↦ Kraus.reindexPhysical (MPOTensor.physicalPairSwapEquiv d)
              (MPSTensor.mapStar (data.blocks k))) i := by
      simp only [MPSTensor.toTensorFromBlocks, Kraus.reindexPhysical]
      rw [show ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
          (Matrix.blockDiagonal' fun k => data.weights k •
            data.blocks k (MPOTensor.physicalPairSwapEquiv d i))).map (starRingEnd ℂ) =
          (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
            ((Matrix.blockDiagonal' fun k => data.weights k •
              data.blocks k (MPOTensor.physicalPairSwapEquiv d i)).map (starRingEnd ℂ)) by
        ext β α
        rfl]
      rw [Matrix.blockDiagonal'_map _ _ (by simp)]
      congr 2
      funext k
      ext β α
      simp [MPSTensor.mapStar, Matrix.map_apply]
    rw [Matrix.map_mul, Matrix.map_mul,
      Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj]),
      hmiddle] at hmap
    exact hmap
  blocks_left_canonical := fun k ↦
    (MPSTensor.leftCanonical_reindexPhysical_equiv
      (MPOTensor.physicalPairSwapEquiv d) _).2
      (MPSTensor.IsLeftCanonical.mapStar (data.blocks_left_canonical k))
  blocks_fixed_point := by
    intro k
    obtain ⟨Λ, hΛpos, hΛdiag, hΛfix⟩ := data.blocks_fixed_point k
    refine ⟨Λ, hΛpos, hΛdiag, ?_⟩
    rw [MPSTensor.transferMap_reindexPhysical_equiv]
    rw [← MPSTensor.map_star_eq_self_of_posDef_isDiag hΛpos hΛdiag,
      MPSTensor.transferMap_mapStar, hΛfix,
      MPSTensor.map_star_eq_self_of_posDef_isDiag hΛpos hΛdiag]

/-- The transported data have the same block count. -/
@[simp] theorem physicalAdjointNormalizedFlattening_r
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) :
    data.physicalAdjointNormalizedFlattening.r = data.r := rfl

/-- The transported data have the same block dimensions. -/
@[simp] theorem physicalAdjointNormalizedFlattening_dim
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) :
    data.physicalAdjointNormalizedFlattening.dim = data.dim := rfl

/-- The transported weights are the conjugates of the original weights. -/
@[simp] theorem physicalAdjointNormalizedFlattening_weights
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) (k : Fin data.r) :
    data.physicalAdjointNormalizedFlattening.weights k = star (data.weights k) := rfl

/-- The transported blocks are conjugated and then physically swapped. -/
@[simp] theorem physicalAdjointNormalizedFlattening_blocks
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) (k : Fin data.r) :
    data.physicalAdjointNormalizedFlattening.blocks k =
      Kraus.reindexPhysical (MPOTensor.physicalPairSwapEquiv d)
        (MPSTensor.mapStar (data.blocks k)) := rfl

/-- The transported ambient coisometry is the entrywise conjugate of the original one. -/
@[simp] theorem physicalAdjointNormalizedFlattening_ambient_coisometry
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) :
    data.physicalAdjointNormalizedFlattening.ambient_coisometry =
      data.ambient_coisometry.map (starRingEnd ℂ) := rfl

/-- Physical adjunction preserves full active support of reduced CFII data. -/
theorem hasFullActiveSupport_physicalAdjointNormalizedFlattening
    (data : CPSVCanonicalFormIIData U.normalizedFlattening)
    (hfull : data.toCPSVCanonicalFormData.HasFullActiveSupport) :
    data.physicalAdjointNormalizedFlattening.toCPSVCanonicalFormData.HasFullActiveSupport := by
  classical
  simp only [MPSTensor.CPSVCanonicalFormData.HasFullActiveSupport]
  change (∑ k : {k : Fin data.r // star (data.weights k) ≠ 0}, data.dim k.1) = D
  let e : {k : Fin data.r // star (data.weights k) ≠ 0} ≃
      data.toCPSVCanonicalFormData.Active :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun k ↦ star_ne_zero)
  apply (e.sum_comp (fun k ↦ data.dim k.1)).trans
  exact hfull

end MPSTensor.CPSVCanonicalFormIIData

namespace MPSTensor.IsCPSVCanonicalFormII

variable {d D : ℕ} {U : MPOTensor d D}

/-- Physical adjunction preserves literal CPSV canonical form II of the normalized flattening.

The literal canonical-form-II structure is from arXiv:1606.00608, Appendix A,
lines 1054--1077. The normalization context is arXiv:1703.09188, equation `Erightleft`,
lines 271--281, and equation `eq:transfer-op`, lines 336--340. -/
theorem physicalAdjointNormalizedFlattening
    (h : MPSTensor.IsCPSVCanonicalFormII U.normalizedFlattening) :
    MPSTensor.IsCPSVCanonicalFormII
      (MPOTensor.physicalAdjointTensor U).normalizedFlattening := by
  obtain ⟨data⟩ := h
  exact ⟨data.physicalAdjointNormalizedFlattening⟩

end MPSTensor.IsCPSVCanonicalFormII
