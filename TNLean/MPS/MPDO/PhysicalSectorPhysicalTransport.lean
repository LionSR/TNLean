/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport

/-!
# Transport of the blocked physical-sector fixed point

This file transports the two-site blocked fixed-point channels from the
sector coordinates of Proposition C.7 back to the original physical tensor.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9, direction (iv) implies (v), and Appendix C.2, lines 1510--1563
  and 1821--1825
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

private noncomputable def physicalBlockOneMap
    (F : PhysicalSectorFactorization K) :
    Matrix (Fin (d * d)) (Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix (Fin (Fintype.card (SectorSiteIndex F) *
        Fintype.card (SectorSiteIndex F)))
        (Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F))) ℂ :=
  Matrix.equivReindexMap
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))).symm ∘ₗ
    singleKrausMap F.physicalCoordinateMatrixTwo ∘ₗ
    Matrix.equivReindexMap (blockedIndexEquiv d)

private noncomputable def physicalBlockOneInverseMap
    (F : PhysicalSectorFactorization K) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F) *
        Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F) *
        Fintype.card (SectorSiteIndex F))) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d)) (Fin (d * d)) ℂ :=
  Matrix.equivReindexMap (blockedIndexEquiv d).symm ∘ₗ
    singleKrausMap F.physicalCoordinateMatrixTwoᴴ ∘ₗ
    Matrix.equivReindexMap
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))

private noncomputable def physicalBlockTwoMap
    (F : PhysicalSectorFactorization K) :
    Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * d) × Fin (d * d)) ℂ →ₗ[ℂ]
      Matrix
        (Fin (Fintype.card (SectorSiteIndex F) *
            Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F) *
            Fintype.card (SectorSiteIndex F)))
        (Fin (Fintype.card (SectorSiteIndex F) *
            Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F) *
            Fintype.card (SectorSiteIndex F))) ℂ :=
  Matrix.equivReindexMap
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F))).symm ∘ₗ
    singleKrausMap F.physicalCoordinateMatrixFour ∘ₗ
    Matrix.equivReindexMap (blockedPairEquiv d)

private noncomputable def physicalBlockTwoInverseMap
    (F : PhysicalSectorFactorization K) :
    Matrix
        (Fin (Fintype.card (SectorSiteIndex F) *
            Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F) *
            Fintype.card (SectorSiteIndex F)))
        (Fin (Fintype.card (SectorSiteIndex F) *
            Fintype.card (SectorSiteIndex F)) ×
          Fin (Fintype.card (SectorSiteIndex F) *
            Fintype.card (SectorSiteIndex F))) ℂ →ₗ[ℂ]
      Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * d) × Fin (d * d)) ℂ :=
  Matrix.equivReindexMap (blockedPairEquiv d).symm ∘ₗ
    singleKrausMap F.physicalCoordinateMatrixFourᴴ ∘ₗ
    Matrix.equivReindexMap
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))

private theorem physicalBlockOneMap_isKrausCPTP
    (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (physicalBlockOneMap F) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP (blockedIndexEquiv d))
      (singleKrausMap_isKrausCPTP F.physicalCoordinateMatrixTwo
        F.physicalCoordinateMatrixTwo_isometry))
    (Matrix.equivReindexMap_isKrausCPTP
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))).symm)

private theorem physicalBlockOneInverseMap_isKrausCPTP
    (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (physicalBlockOneInverseMap F) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP
        (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))))
      (singleKrausMap_isKrausCPTP F.physicalCoordinateMatrixTwoᴴ (by
        simpa using F.physicalCoordinateMatrixTwo_coisometry)))
    (Matrix.equivReindexMap_isKrausCPTP (blockedIndexEquiv d).symm)

private theorem physicalBlockTwoMap_isKrausCPTP
    (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (physicalBlockTwoMap F) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP (blockedPairEquiv d))
      (singleKrausMap_isKrausCPTP F.physicalCoordinateMatrixFour
        F.physicalCoordinateMatrixFour_isometry))
    (Matrix.equivReindexMap_isKrausCPTP
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F))).symm)

private theorem physicalBlockTwoInverseMap_isKrausCPTP
    (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (physicalBlockTwoInverseMap F) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP
        (blockedPairEquiv (Fintype.card (SectorSiteIndex F))))
      (singleKrausMap_isKrausCPTP F.physicalCoordinateMatrixFourᴴ (by
        simpa using F.physicalCoordinateMatrixFour_coisometry)))
    (Matrix.equivReindexMap_isKrausCPTP (blockedPairEquiv d).symm)

private theorem physicalBlockOneMap_closure
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ) :
    physicalBlockOneMap F (physClose1 (blockTwo K) X) =
      physClose1 (blockTwo F.sectorCoordinateTensor) X := by
  change Matrix.reindex
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))).symm
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))).symm
      (singleKrausMap F.physicalCoordinateMatrixTwo
        (Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d)
          (physClose1 (blockTwo K) X))) = _
  rw [show Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d)
      (physClose1 (blockTwo K) X) = physClose2 K X by
    exact LinearMap.congr_fun (physClose1_blockTwo_eq_physClose2 K) X]
  rw [F.physicalCoordinateMatrixTwo_physClose2]
  rw [← show Matrix.reindex
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
      (physClose1 (blockTwo F.sectorCoordinateTensor) X) =
        physClose2 F.sectorCoordinateTensor X by
    exact LinearMap.congr_fun
      (physClose1_blockTwo_eq_physClose2 F.sectorCoordinateTensor) X]
  simp

private theorem physicalBlockOneInverseMap_closure
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ) :
    physicalBlockOneInverseMap F
        (physClose1 (blockTwo F.sectorCoordinateTensor) X) =
      physClose1 (blockTwo K) X := by
  change Matrix.reindex (blockedIndexEquiv d).symm (blockedIndexEquiv d).symm
      (singleKrausMap F.physicalCoordinateMatrixTwoᴴ
        (Matrix.reindex
          (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
          (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
          (physClose1 (blockTwo F.sectorCoordinateTensor) X))) = _
  rw [show Matrix.reindex
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
      (physClose1 (blockTwo F.sectorCoordinateTensor) X) =
        physClose2 F.sectorCoordinateTensor X by
    exact LinearMap.congr_fun
      (physClose1_blockTwo_eq_physClose2 F.sectorCoordinateTensor) X]
  rw [F.physicalCoordinateMatrixTwo_conjTranspose_physClose2]
  rw [← show Matrix.reindex (blockedIndexEquiv d) (blockedIndexEquiv d)
      (physClose1 (blockTwo K) X) = physClose2 K X by
    exact LinearMap.congr_fun (physClose1_blockTwo_eq_physClose2 K) X]
  simp

private theorem physicalBlockTwoMap_closure
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ) :
    physicalBlockTwoMap F (physClose2 (blockTwo K) X) =
      physClose2 (blockTwo F.sectorCoordinateTensor) X := by
  change Matrix.reindex
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F))).symm
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F))).symm
      (singleKrausMap F.physicalCoordinateMatrixFour
        (Matrix.reindex (blockedPairEquiv d) (blockedPairEquiv d)
          (physClose2 (blockTwo K) X))) = _
  rw [show Matrix.reindex (blockedPairEquiv d) (blockedPairEquiv d)
      (physClose2 (blockTwo K) X) = physClose4 K X by
    exact LinearMap.congr_fun (physClose2_blockTwo_eq_physClose4 K) X]
  rw [F.physicalCoordinateMatrixFour_physClose4]
  rw [← show Matrix.reindex
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
      (physClose2 (blockTwo F.sectorCoordinateTensor) X) =
        physClose4 F.sectorCoordinateTensor X by
    exact LinearMap.congr_fun
      (physClose2_blockTwo_eq_physClose4 F.sectorCoordinateTensor) X]
  simp

private theorem physicalBlockTwoInverseMap_closure
    (F : PhysicalSectorFactorization K) (X : Matrix (Fin D) (Fin D) ℂ) :
    physicalBlockTwoInverseMap F
        (physClose2 (blockTwo F.sectorCoordinateTensor) X) =
      physClose2 (blockTwo K) X := by
  change Matrix.reindex (blockedPairEquiv d).symm (blockedPairEquiv d).symm
      (singleKrausMap F.physicalCoordinateMatrixFourᴴ
        (Matrix.reindex
          (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
          (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
          (physClose2 (blockTwo F.sectorCoordinateTensor) X))) = _
  rw [show Matrix.reindex
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
      (physClose2 (blockTwo F.sectorCoordinateTensor) X) =
        physClose4 F.sectorCoordinateTensor X by
    exact LinearMap.congr_fun
      (physClose2_blockTwo_eq_physClose4 F.sectorCoordinateTensor) X]
  rw [F.physicalCoordinateMatrixFour_conjTranspose_physClose4]
  rw [← show Matrix.reindex (blockedPairEquiv d) (blockedPairEquiv d)
      (physClose2 (blockTwo K) X) = physClose4 K X by
    exact LinearMap.congr_fun (physClose2_blockTwo_eq_physClose4 K) X]
  simp

/-- The original two-site blocked tensor is a renormalization fixed point.
The channels are transported from the sector-coordinate channels through the
physical isometry of Proposition C.7.

**Local fix (zero-weight quotient):** the refinement channel uses the completed
zero-weight preparation branch. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

**Local fix (implication label):** Appendix line 1824 labels this construction
as direction (iii) implies (v), while the theorem statement and the local
structure used here give direction (iv) implies (v). Documented in
`docs/paper-gaps/cpgsv17_mpdo_theorem_4_9_implication_label.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 645--659; Theorem 4.9,
direction (iv) implies (v), lines 851--893; and Appendix C.2, lines 1510--1563
and 1821--1825. -/
theorem NeighboringTraceFactorization.blockTwo_isRFPViaTS
    (H : NeighboringTraceFactorization F) : IsRFPViaTS (blockTwo K) := by
  rcases H.blockTwo_sectorCoordinateTensor_isRFPViaTS with
    ⟨sectorS, sectorT, hSectorS, hSectorT, hSectorSClose, hSectorTClose⟩
  let rawS := F.physicalBlockOneInverseMap ∘ₗ sectorS ∘ₗ F.physicalBlockTwoMap
  let rawT := F.physicalBlockTwoInverseMap ∘ₗ sectorT ∘ₗ F.physicalBlockOneMap
  refine ⟨rawS, rawT, ?_, ?_, ?_, ?_⟩
  · exact isKrausCPTP_comp
      (isKrausCPTP_comp F.physicalBlockTwoMap_isKrausCPTP hSectorS)
      F.physicalBlockOneInverseMap_isKrausCPTP
  · exact isKrausCPTP_comp
      (isKrausCPTP_comp F.physicalBlockOneMap_isKrausCPTP hSectorT)
      F.physicalBlockTwoInverseMap_isKrausCPTP
  · intro X
    change F.physicalBlockOneInverseMap
      (sectorS (F.physicalBlockTwoMap (physClose2 (blockTwo K) X))) = _
    rw [F.physicalBlockTwoMap_closure, hSectorSClose,
      F.physicalBlockOneInverseMap_closure]
  · intro X
    change F.physicalBlockTwoInverseMap
      (sectorT (F.physicalBlockOneMap (physClose1 (blockTwo K) X))) = _
    rw [F.physicalBlockOneMap_closure, hSectorTClose,
      F.physicalBlockTwoInverseMap_closure]


end MPOTensor.PhysicalSectorFactorization
