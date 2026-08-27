/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorCoordinateTransport

/-!
# Transport of the blocked physical-sector fixed point

This file transports the two-site blocked fixed-point channels from one
supplied sector factorization of Proposition C.7 back to the original physical
tensor.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition C.7, Appendix C.2, lines 1510--1563, and the twice-applied
  channel observation at lines 1821--1825
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- Transport a channel through a change of blocked physical coordinates:
relabel the source index along `eS`, conjugate by `V`, then relabel the target
index back along `eT`. -/
private noncomputable def blockTransportMap {a b a' b' : Type*}
    [Fintype b] [Fintype b'] (eS : a ≃ b) (eT : a' ≃ b') (V : Matrix b' b ℂ) :
    Matrix a a ℂ →ₗ[ℂ] Matrix a' a' ℂ :=
  Matrix.equivReindexMap eT.symm ∘ₗ singleKrausMap V ∘ₗ
    Matrix.equivReindexMap eS

/-- A coordinate transport by an isometry is trace-preserving completely
positive. -/
private theorem blockTransportMap_isKrausCPTP {a b a' b' : Type*}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b']
    (eS : a ≃ b) (eT : a' ≃ b') (V : Matrix b' b ℂ) (hV : Vᴴ * V = 1) :
    IsKrausCPTP (blockTransportMap eS eT V) := by
  classical
  exact isKrausCPTP_comp
    (isKrausCPTP_comp (Matrix.equivReindexMap_isKrausCPTP eS)
      (singleKrausMap_isKrausCPTP V hV))
    (Matrix.equivReindexMap_isKrausCPTP eT.symm)

private noncomputable def physicalBlockOneMap
    (F : PhysicalSectorFactorization K) :=
  blockTransportMap (blockedIndexEquiv d)
    (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
    F.physicalCoordinateMatrixTwo

private noncomputable def physicalBlockOneInverseMap
    (F : PhysicalSectorFactorization K) :=
  blockTransportMap (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
    (blockedIndexEquiv d) F.physicalCoordinateMatrixTwoᴴ

private noncomputable def physicalBlockTwoMap
    (F : PhysicalSectorFactorization K) :=
  blockTransportMap (blockedPairEquiv d)
    (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
    F.physicalCoordinateMatrixFour

private noncomputable def physicalBlockTwoInverseMap
    (F : PhysicalSectorFactorization K) :=
  blockTransportMap (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
    (blockedPairEquiv d) F.physicalCoordinateMatrixFourᴴ

private theorem physicalBlockOneMap_isKrausCPTP
    (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (physicalBlockOneMap F) :=
  blockTransportMap_isKrausCPTP (blockedIndexEquiv d)
    (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
    F.physicalCoordinateMatrixTwo F.physicalCoordinateMatrixTwo_isometry

private theorem physicalBlockOneInverseMap_isKrausCPTP
    (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (physicalBlockOneInverseMap F) :=
  blockTransportMap_isKrausCPTP
    (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
    (blockedIndexEquiv d) F.physicalCoordinateMatrixTwoᴴ
    (by simpa using F.physicalCoordinateMatrixTwo_coisometry)

private theorem physicalBlockTwoMap_isKrausCPTP
    (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (physicalBlockTwoMap F) :=
  blockTransportMap_isKrausCPTP (blockedPairEquiv d)
    (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
    F.physicalCoordinateMatrixFour F.physicalCoordinateMatrixFour_isometry

private theorem physicalBlockTwoInverseMap_isKrausCPTP
    (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (physicalBlockTwoInverseMap F) :=
  blockTransportMap_isKrausCPTP
    (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
    (blockedPairEquiv d) F.physicalCoordinateMatrixFourᴴ
    (by simpa using F.physicalCoordinateMatrixFour_coisometry)

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
  rw [physClose1_blockTwo_reindex_eq_physClose2 K X]
  rw [F.physicalCoordinateMatrixTwo_physClose2]
  rw [← physClose1_blockTwo_reindex_eq_physClose2 F.sectorCoordinateTensor X]
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
  rw [physClose1_blockTwo_reindex_eq_physClose2 F.sectorCoordinateTensor X]
  rw [F.physicalCoordinateMatrixTwo_conjTranspose_physClose2]
  rw [← physClose1_blockTwo_reindex_eq_physClose2 K X]
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
  rw [physClose2_blockTwo_reindex_eq_physClose4 K X]
  rw [F.physicalCoordinateMatrixFour_physClose4]
  rw [← physClose2_blockTwo_reindex_eq_physClose4 F.sectorCoordinateTensor X]
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
  rw [physClose2_blockTwo_reindex_eq_physClose4 F.sectorCoordinateTensor X]
  rw [F.physicalCoordinateMatrixFour_conjTranspose_physClose4]
  rw [← physClose2_blockTwo_reindex_eq_physClose4 K X]
  simp

/-- The original two-site blocked tensor is a renormalization fixed point.
The channels are transported from the sector-coordinate channels through the
physical isometry of Proposition C.7.

**Local fix (zero-weight quotient):** the refinement channel uses the completed
zero-weight preparation branch. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

**Local fix (cyclic implication labels):** Appendix lines 1822--1824 assign the
wrong conditions to the four propositions used in the closing proof. This
theorem instead follows the one-factorization construction of Proposition C.7
and the twice-applied channel observation at lines 1821--1825. Documented in
`docs/paper-gaps/cpgsv17_mpdo_theorem_4_9_implication_label.tex`.

**Scope restriction (single supplied factorization):** this theorem constructs
the channels for one `PhysicalSectorFactorization` and its neighboring trace
data. Theorem 4.9(iv) supplies such data separately for each outer BNT element;
assembling the resulting channels by the mutually orthogonal outer physical
supports is proved in `TNLean/MPS/MPDO/BNTFactorizationChannels.lean`.
Documented in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 645--659; Proposition C.7,
lines 1510--1563; and the twice-applied channel observation at lines
1821--1825. -/
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
