/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorPhysicalMaps
import TNLean.MPS.MPDO.RFPViaTS

/-!
# Two-site blocked renormalization of the physical-sector tensor

This file composes the physical-coordinate channels of Proposition C.7 twice.
The resulting channels exchange the two-site and four-site closures of the
physical-sector tensor associated with one supplied neighboring trace
factorization. Decoding the physical indices of a two-site block then exhibits
that two-site blocked tensor as a renormalization fixed point.

The result concerns the tensor in the physical-sector coordinates selected by
the isometry in Proposition C.7. Transport through that isometry to the original
physical tensor is not asserted here.

**Scope restriction (single supplied factorization):** Theorem 4.9(iv) supplies
this data separately for every outer BNT element. This file assumes one
`NeighboringTraceFactorization`; it neither assembles the resulting channel
pairs along the outer physical supports nor proves the full implication to
Theorem 4.9(v). Documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

**Local fix (cyclic implication labels):** The concluding proof at source
lines 1822--1824 assigns the wrong conditions to Propositions `prop2to3`,
`prop3to4`, `prop4to2`, and `prop2to5`. The declarations below cite the
one-factorization construction of Proposition C.7 and its twice-applied channel
observation directly, rather than assigning it a false implication label.
Documented in
`docs/paper-gaps/cpgsv17_mpdo_theorem_4_9_implication_label.tex`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Proposition C.7, Appendix C.2, source lines 1510--1563, composed twice as
  observed at source lines 1821--1825; Theorem 4.9, source lines 851--893
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- The twice-applied physical refinement channel: first refine two physical
sites to three, then refine the first two of those three sites to obtain four.

This is the map denoted \(\mathcal T^2\) at arXiv:1606.00608, Appendix C.2,
line 1824. It is the twice-applied refinement channel of Proposition C.7,
source lines 1510--1545. -/
noncomputable def NeighboringTraceFactorization.physicalTSquaredMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F))) ℂ →ₗ[ℂ]
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F)))))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F))))) ℂ :=
  H.localizedPhysicalTMap ∘ₗ H.physicalTMap

/-- The twice-applied physical refinement map is trace-preserving and
completely positive.

Source: arXiv:1606.00608, Proposition C.7, source lines 1510--1545, composed
twice as at Appendix C.2, lines 1821--1825. -/
theorem NeighboringTraceFactorization.physicalTSquaredMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) :
    IsKrausCPTP H.physicalTSquaredMap := by
  exact isKrausCPTP_comp H.physicalTMap_isKrausCPTP
    H.localizedPhysicalTMap_isKrausCPTP

/-- The twice-applied physical refinement sends the two-site closure of the
physical-sector tensor to its four-site closure.

**Local fix (zero-weight quotient):** this identity uses the completed
zero-weight preparation branch of the refinement channel. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Proposition C.7, source lines 1510--1545, composed
twice as at Appendix C.2, lines 1821--1825. -/
theorem NeighboringTraceFactorization.physicalTSquaredMap_twoSiteClosure_eq_fourSiteClosure
    (H : NeighboringTraceFactorization F) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.physicalTSquaredMap (physClose2 F.sectorCoordinateTensor X) =
      physClose4 F.sectorCoordinateTensor X := by
  rw [NeighboringTraceFactorization.physicalTSquaredMap, LinearMap.comp_apply,
    H.physicalTMap_twoSiteClosure_eq_threeSiteClosure,
    H.localizedPhysicalTMap_threeSiteClosure_eq_fourSiteClosure]

/-- The twice-applied physical coarse-graining channel: first coarse-grain the
first three of four physical sites, then coarse-grain the remaining three sites
to two.

This is the map denoted \(\mathcal S^2\) at arXiv:1606.00608, Appendix C.2,
line 1824. It is the twice-applied coarse-graining channel of Proposition C.7,
source lines 1547--1563. -/
noncomputable def NeighboringTraceFactorization.physicalSSquaredMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F)))))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        (Fin (Fintype.card (SectorSiteIndex F)) ×
          (Fin (Fintype.card (SectorSiteIndex F)) ×
            Fin (Fintype.card (SectorSiteIndex F))))) ℂ →ₗ[ℂ]
    Matrix (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F))) ℂ :=
  H.physicalSMap ∘ₗ H.localizedPhysicalSMap

/-- The twice-applied physical coarse-graining map is trace-preserving and
completely positive.

Source: arXiv:1606.00608, Proposition C.7, source lines 1547--1563, composed
twice as at Appendix C.2, lines 1821--1825. -/
theorem NeighboringTraceFactorization.physicalSSquaredMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) :
    IsKrausCPTP H.physicalSSquaredMap := by
  exact isKrausCPTP_comp H.localizedPhysicalSMap_isKrausCPTP
    H.physicalSMap_isKrausCPTP

/-- The twice-applied physical coarse-graining sends the four-site closure of
the physical-sector tensor to its two-site closure.

Source: arXiv:1606.00608, Proposition C.7, source lines 1547--1563, composed
twice as at Appendix C.2, lines 1821--1825. -/
theorem NeighboringTraceFactorization.physicalSSquaredMap_fourSiteClosure_eq_twoSiteClosure
    (H : NeighboringTraceFactorization F) (X : Matrix (Fin D) (Fin D) ℂ) :
    H.physicalSSquaredMap (physClose4 F.sectorCoordinateTensor X) =
      physClose2 F.sectorCoordinateTensor X := by
  rw [NeighboringTraceFactorization.physicalSSquaredMap, LinearMap.comp_apply,
    H.localizedPhysicalSMap_fourSiteClosure_eq_threeSiteClosure,
    H.physicalSMap_threeSiteClosure_eq_twoSiteClosure]

/-- The refinement channel on two-site blocked physical indices, obtained from
\(\mathcal T^2\) by the canonical decoding of one and two blocked sites.

Source: arXiv:1606.00608, Appendix C.2, lines 1821--1825, using the refinement
channel of Proposition C.7, lines 1510--1545. -/
private noncomputable def NeighboringTraceFactorization.blockedPhysicalTMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F) *
        Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F) *
        Fintype.card (SectorSiteIndex F))) ℂ →ₗ[ℂ]
    Matrix (Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F))) ℂ :=
  Matrix.equivReindexMap
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F))).symm ∘ₗ
    H.physicalTSquaredMap ∘ₗ
    Matrix.equivReindexMap
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))

/-- The coarse-graining channel on two-site blocked physical indices, obtained
from \(\mathcal S^2\) by the canonical decoding of one and two blocked sites.

Source: arXiv:1606.00608, Appendix C.2, lines 1821--1825, using the
coarse-graining channel of Proposition C.7, lines 1547--1563. -/
private noncomputable def NeighboringTraceFactorization.blockedPhysicalSMap
    (H : NeighboringTraceFactorization F) :
    Matrix (Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F)) ×
        Fin (Fintype.card (SectorSiteIndex F) *
          Fintype.card (SectorSiteIndex F))) ℂ →ₗ[ℂ]
    Matrix (Fin (Fintype.card (SectorSiteIndex F) *
        Fintype.card (SectorSiteIndex F)))
      (Fin (Fintype.card (SectorSiteIndex F) *
        Fintype.card (SectorSiteIndex F))) ℂ :=
  Matrix.equivReindexMap
      (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))).symm ∘ₗ
    H.physicalSSquaredMap ∘ₗ
    Matrix.equivReindexMap
      (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))

/-- The two-site blocked physical-sector tensor is a renormalization fixed
point. The channels are the maps \(\mathcal S^2\) and \(\mathcal T^2\) of the
source, transported only through the canonical blocked-index equivalences.

**Local fix (zero-weight quotient):** the refinement identity used here has
the completed zero-weight preparation branch. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

This statement is restricted to the physical-sector tensor; it does not
transport the channels through the physical isometry to the original tensor.

**Scope restriction (physical coordinates):** the source conclusion concerns
the original blocked tensor, whereas this theorem concerns its sector-coordinate
form. Documented in
`docs/paper-gaps/cpgsv17_mpdo_blocked_rfp_physical_transport.tex`. Elimination:
transport the two channels through the two- and four-site physical unitaries.

**Scope restriction (single supplied factorization):** this theorem assumes one
`NeighboringTraceFactorization`. Theorem 4.9(iv) supplies such a factorization
separately for every outer BNT element; their projector-controlled channel
assembly is not proved here. Documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.

Source: arXiv:1606.00608, Definition 4.1, lines 645--659; Proposition C.7,
lines 1510--1563; and the twice-applied channel observation at Appendix C.2,
lines 1821--1825. -/
theorem NeighboringTraceFactorization.blockTwo_sectorCoordinateTensor_isRFPViaTS
    (H : NeighboringTraceFactorization F) :
    IsRFPViaTS (blockTwo F.sectorCoordinateTensor) := by
  refine ⟨H.blockedPhysicalSMap, H.blockedPhysicalTMap, ?_, ?_, ?_, ?_⟩
  · exact isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP
          (blockedPairEquiv (Fintype.card (SectorSiteIndex F))))
        H.physicalSSquaredMap_isKrausCPTP)
      (Matrix.equivReindexMap_isKrausCPTP
        (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))).symm)
  · exact isKrausCPTP_comp
      (isKrausCPTP_comp
        (Matrix.equivReindexMap_isKrausCPTP
          (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))))
        H.physicalTSquaredMap_isKrausCPTP)
      (Matrix.equivReindexMap_isKrausCPTP
        (blockedPairEquiv (Fintype.card (SectorSiteIndex F))).symm)
  · intro X
    change Matrix.reindex
        (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))).symm
        (blockedIndexEquiv (Fintype.card (SectorSiteIndex F))).symm
        (H.physicalSSquaredMap
          (Matrix.reindex
            (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
            (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
            (physClose2 (blockTwo F.sectorCoordinateTensor) X))) =
      physClose1 (blockTwo F.sectorCoordinateTensor) X
    rw [show Matrix.reindex
        (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
        (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
        (physClose2 (blockTwo F.sectorCoordinateTensor) X) =
      physClose4 F.sectorCoordinateTensor X by
        exact LinearMap.congr_fun
          (physClose2_blockTwo_eq_physClose4 F.sectorCoordinateTensor) X]
    rw [H.physicalSSquaredMap_fourSiteClosure_eq_twoSiteClosure]
    rw [← show Matrix.reindex
        (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
        (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
        (physClose1 (blockTwo F.sectorCoordinateTensor) X) =
      physClose2 F.sectorCoordinateTensor X by
        exact LinearMap.congr_fun
          (physClose1_blockTwo_eq_physClose2 F.sectorCoordinateTensor) X]
    simp
  · intro X
    change Matrix.reindex
        (blockedPairEquiv (Fintype.card (SectorSiteIndex F))).symm
        (blockedPairEquiv (Fintype.card (SectorSiteIndex F))).symm
        (H.physicalTSquaredMap
          (Matrix.reindex
            (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
            (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
            (physClose1 (blockTwo F.sectorCoordinateTensor) X))) =
      physClose2 (blockTwo F.sectorCoordinateTensor) X
    rw [show Matrix.reindex
        (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
        (blockedIndexEquiv (Fintype.card (SectorSiteIndex F)))
        (physClose1 (blockTwo F.sectorCoordinateTensor) X) =
      physClose2 F.sectorCoordinateTensor X by
        exact LinearMap.congr_fun
          (physClose1_blockTwo_eq_physClose2 F.sectorCoordinateTensor) X]
    rw [H.physicalTSquaredMap_twoSiteClosure_eq_fourSiteClosure]
    rw [← show Matrix.reindex
        (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
        (blockedPairEquiv (Fintype.card (SectorSiteIndex F)))
        (physClose2 (blockTwo F.sectorCoordinateTensor) X) =
      physClose4 F.sectorCoordinateTensor X by
        exact LinearMap.congr_fun
          (physClose2_blockTwo_eq_physClose4 F.sectorCoordinateTensor) X]
    simp

end MPOTensor.PhysicalSectorFactorization
