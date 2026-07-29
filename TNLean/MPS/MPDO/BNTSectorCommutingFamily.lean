/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.GSNNCHOrthogonalSectors
import TNLean.MPS.MPDO.PhysicalSupportProductTransport

/-!
# Commuting products on the BNT physical sectors

The positive commuting bond of Proposition C.8 may be constructed on the
injective restriction of each absorbed BNT representative and then included
in the original physical space. The included bonds remain supported on their
pairwise orthogonal BNT sectors and realize the sector MPOs exactly on every
periodic chain of length at least two.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, and Proposition
  `prop3to4`, lines 1733--1792
-/

namespace MPOTensor

variable {d D : ℕ}

/-- Saturation of the area law for every absorbed BNT representative gives a
family of positive commuting bond products supported on the corresponding
pairwise orthogonal BNT projectors.

The hypotheses preceding `hSectorSAL` are precisely the data selecting the
BNT physical projectors. The sectorwise SAL hypothesis is established from
the simple-MPDO hypotheses in
`commonWeightAbsorbedBasisMPOTensor_isSAL_of_sameMPV₂Pos`.

This is a sufficient construction of the sector family used in the later
GSNNCH assembly.

**Scope restriction (projector-selection and sectorwise-SAL hypotheses):** The
theorem assumes more than the five blockwise identities printed in CPSV16
Proposition `prop3to4`.  See
`docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
theorem nonempty_orthogonalCommutingSectorFamily_of_bntSectorSAL
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ)
    (hη : EtaStructure ρ) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSectorSAL : ∀ s : Fin S.basisCount,
      IsSAL (commonWeightAbsorbedBasisMPOTensor S hWeight s)) :
    Nonempty (OrthogonalCommutingSectorFamily
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s)) := by
  classical
  let restriction : (s : Fin S.basisCount) →
      PhysicalSupportRestrictionData
        (bntSectorProjection hC hρ hη hR s)
        (commonWeightAbsorbedBasisMPOTensor S hWeight s) :=
    fun s ↦ Classical.choice
      (nonempty_physicalSupportRestrictionData_commonWeightAbsorbedBasis
        S hWeight hC hρ hη hR hSpan s)
  let data : (s : Fin S.basisCount) → EtaLocalStructureData
      (commonWeightAbsorbedBasisMPOTensor S hWeight s) :=
    fun s ↦ Classical.choose
      ((restriction s).exists_etaLocalStructureData_lifted_supported
        (hSectorSAL s))
  have hdata : ∀ s : Fin S.basisCount,
      twoSiteSectorProjection (bntSectorProjection hC hρ hη hR s) *
          (data s).bondData.bond *
          twoSiteSectorProjection (bntSectorProjection hC hρ hη hR s) =
            (data s).bondData.bond ∧
        ∀ N (hN : 2 ≤ N),
          mpo (commonWeightAbsorbedBasisMPOTensor S hWeight s) N =
            ((data s).bondData.toCommutingFormData hN).product :=
    fun s ↦ Classical.choose_spec
      ((restriction s).exists_etaLocalStructureData_lifted_supported
        (hSectorSAL s))
  exact ⟨{
    projection := fun s ↦ bntSectorProjection hC hρ hη hR s
    projection_isOrthogonal := fun s ↦
      bntSectorProjection_isOrthogonal hC hρ hη hR s
    projection_orthogonal := fun hst ↦
      bntSectorProjection_mul_eq_zero hC hρ hη hR hst
    bondData := fun s ↦ (data s).bondData
    bond_supported := fun s ↦ (hdata s).1
    realizes_mpo := fun s N hN ↦ (hdata s).2 N hN }⟩

/-- Once the absorbed BNT representatives satisfy SAL, their supported
commuting products assemble with the natural BNT multiplicities to give the
GSNNCH form of the original tensor.

This is a sufficient-condition theorem obtained after the physical projectors,
sectorwise SAL witnesses, supported bonds, and exact sector products have been
constructed.

**Scope restriction (later BNT-sector assembly):** The hypotheses are stronger
than the five blockwise identities printed in CPSV16 Proposition `prop3to4`.
See `docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`. -/
theorem hasGSNNCHForm_of_bntSectorSAL
    (M : MPOTensor d D) (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    {R : (s : Fin S.basisCount) →
      Matrix (Fin (S.basisDim s)) (Fin (S.basisDim s)) ℂ}
    {ρ : Matrix (Fin d × Fin d × Fin d) (Fin d × Fin d × Fin d) ℂ}
    {C : Matrix (MPSTensor.BlockEntryIndex S.basisDim) (Fin d × Fin d) ℂ}
    (hC : MPSTensor.IsMPOBlockLeftInverse
      (fun j ↦ S.basisMPOTensor j) C)
    (hρ : IsThreeSiteFamilyClosure (fun j ↦ S.basisMPOTensor j) R ρ)
    (hη : EtaStructure ρ) (hR : ∀ s : Fin S.basisCount, R s ≠ 0)
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hSectorSAL : ∀ s : Fin S.basisCount,
      IsSAL (commonWeightAbsorbedBasisMPOTensor S hWeight s)) :
    HasGSNNCHForm M := by
  obtain ⟨F⟩ :=
    nonempty_orthogonalCommutingSectorFamily_of_bntSectorSAL
      S hWeight hC hρ hη hR hSpan hSectorSAL
  exact hasGSNNCHForm_of_commonWeightAbsorbedBasisMPOTensor
    M S hM hWeight F

end MPOTensor
