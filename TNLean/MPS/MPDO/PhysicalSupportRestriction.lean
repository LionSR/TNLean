/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.ProjectorClosureDecomposition
import TNLean.MPS.MPDO.BNTProjectorSelection
import TNLean.MPS.MPDO.SimpleLocalStructure

/-!
# Restriction to an orthogonal physical sector

An MPO tensor supported on an orthogonal one-site projection may be regarded
as a tensor on the range of that projection.  This file records the finite
dimensional support isometry, the exact reconstruction in the ambient
physical space, and preservation of injectivity under restriction.

The construction is the range restriction used before applying the injective
part of Proposition C.8 to each BNT sector in Appendix C.2.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `PjKiPj` and `generateMPDO`, lines 1733--1770
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d e D : ℕ}

open PhysicalSectorFactorization

/-- If an ambient tensor is obtained from a smaller tensor by a physical
coordinate change, then injectivity of the ambient tensor implies injectivity
of the smaller tensor. -/
theorem isInjective_of_eq_changePhysicalBasis
    (V : Matrix (Fin d) (Fin e) ℂ) (K : MPOTensor e D) (M : MPOTensor d D)
    (hM : M = changePhysicalBasis V K) (hInjective : M.IsInjective) :
    K.IsInjective := by
  rw [IsInjective, MPSTensor.IsInjective, eq_top_iff]
  rw [← hInjective]
  apply Submodule.span_le.mpr
  rintro X ⟨ij, rfl⟩
  rw [hM]
  change changePhysicalBasis V K ij.divNat ij.modNat ∈
    Submodule.span ℂ (Set.range K.toMPSTensor)
  rw [changePhysicalBasis_apply_eq_sum]
  apply Submodule.sum_mem
  intro p _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨finProdFinEquiv (p.1, p.2), by
    simp only [toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
      MPSTensor.finProdFinEquiv_modNat]⟩

/-- Data identifying an MPO tensor with its restriction to the range of an
orthogonal one-site projection. -/
structure PhysicalSupportRestrictionData
    (P : Matrix (Fin d) (Fin d) ℂ) (K : MPOTensor d D) where
  /-- Dimension of the physical sector. -/
  supportDim : ℕ
  /-- Isometric inclusion of the physical sector into the ambient space. -/
  inclusion : Matrix (Fin d) (Fin supportDim) ℂ
  /-- The columns of the inclusion are orthonormal. -/
  inclusion_isometry : inclusionᴴ * inclusion = 1
  /-- The range projection of the inclusion is the prescribed sector
  projection. -/
  inclusion_range : inclusion * inclusionᴴ = P
  /-- The tensor restricted to the sector range is injective. -/
  restricted_injective :
    (changePhysicalBasis inclusionᴴ K).IsInjective
  /-- Restriction followed by inclusion recovers the ambient tensor exactly. -/
  reembed :
    changePhysicalBasis inclusion (changePhysicalBasis inclusionᴴ K) = K

/-- An injective tensor fixed by an orthogonal physical projection admits an
injective restriction to the range of that projection.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and
`generateMPDO`, lines 1733--1770. -/
theorem exists_physicalSupportRestrictionData
    (P : Matrix (Fin d) (Fin d) ℂ) (K : MPOTensor d D)
    (hP : IsOrthogonalProjection P) (hSupport : changePhysicalBasis P K = K)
    (hInjective : K.IsInjective) :
    Nonempty (PhysicalSupportRestrictionData P K) := by
  obtain ⟨n, V, _hn, hV, hRange⟩ := hP.exists_support_isometry
  have hreembed : changePhysicalBasis V (changePhysicalBasis Vᴴ K) = K := by
    rw [changePhysicalBasis_changePhysicalBasis]
    rw [hRange, hSupport]
  exact ⟨{
    supportDim := n
    inclusion := V
    inclusion_isometry := hV
    inclusion_range := hRange
    restricted_injective :=
      isInjective_of_eq_changePhysicalBasis V
        (changePhysicalBasis Vᴴ K) K hreembed.symm hInjective
    reembed := hreembed }⟩

/-- Two-sided absorption of every physical slice by an orthogonal projection
implies invariance under compression by that projection.

Source: arXiv:1606.00608, Appendix C.2, equation `PjKiPj`, lines 1680--1691. -/
theorem changePhysicalBasis_eq_self_of_twoSided_physicalSlice
    (P : Matrix (Fin d) (Fin d) ℂ) (K : MPOTensor d D)
    (hP : IsOrthogonalProjection P)
    (hSupport : ∀ β α, P * physicalSlice K β α = physicalSlice K β α ∧
      physicalSlice K β α * P = physicalSlice K β α) :
    changePhysicalBasis P K = K := by
  ext i j β α
  change (P * physicalSlice K β α * Pᴴ) i j = physicalSlice K β α i j
  rw [hP.1.eq, (hSupport β α).1, (hSupport β α).2]

/-- An injective tensor whose physical slices are absorbed on both sides by an
orthogonal projection has an injective realization on the range of that projection.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and `generateMPDO`,
lines 1680--1691 and 1733--1770. -/
theorem nonempty_physicalSupportRestrictionData_of_twoSided_physicalSlice
    (P : Matrix (Fin d) (Fin d) ℂ) (K : MPOTensor d D)
    (hP : IsOrthogonalProjection P) (hInjective : K.IsInjective)
    (hSupport : ∀ β α, P * physicalSlice K β α = physicalSlice K β α ∧
      physicalSlice K β α * P = physicalSlice K β α) :
    Nonempty (PhysicalSupportRestrictionData P K) :=
  exists_physicalSupportRestrictionData P K hP
    (changePhysicalBasis_eq_self_of_twoSided_physicalSlice P K hP hSupport)
    hInjective

/-- The restriction of an injective tensor to an orthogonal projection that
absorbs every physical slice on both sides.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj` and `generateMPDO`,
lines 1680--1691 and 1733--1770. -/
noncomputable def physicalSupportRestrictionDataOfTwoSidedPhysicalSlice
    (P : Matrix (Fin d) (Fin d) ℂ) (K : MPOTensor d D)
    (hP : IsOrthogonalProjection P) (hInjective : K.IsInjective)
    (hSupport : ∀ β α, P * physicalSlice K β α = physicalSlice K β α ∧
      physicalSlice K β α * P = physicalSlice K β α) :
    PhysicalSupportRestrictionData P K :=
  Classical.choice
    (nonempty_physicalSupportRestrictionData_of_twoSided_physicalSlice
      P K hP hInjective hSupport)

/-- The common-weight-absorbed BNT representative is injective after the
source's common blocking.

Source: arXiv:1606.00608, Appendix C.2, equation `CFK`, lines 1660--1665. -/
theorem commonWeightAbsorbedBasisMPOTensor_isInjective
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (s : Fin S.basisCount) :
    (commonWeightAbsorbedBasisMPOTensor S hWeight s).IsInjective := by
  rw [IsInjective, commonWeightAbsorbedBasisMPOTensor_toMPSTensor]
  exact (hSpan.isInjective_one s).smul (S.commonWeight_ne_zero hWeight s)

/-- Each common-weight-absorbed BNT representative has an injective
realization on the range of its matching physical-sector projector.

This is the range restriction used before applying Proposition C.8 inside
each outer BNT sector.  The theorem introduces no nonvanishing or positivity
hypothesis beyond the data already used to construct the source projector.

**Scope restriction (closing matrices):** the generic statement retains the
nonzero-closing hypothesis used to construct the sector projectors.  The
source specialization derives this hypothesis in
`BNTThreeSiteReducedClosure.lean`.  This intermediate restriction is recorded
in `docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`.

Source: arXiv:1606.00608, Appendix C.2, equations `PjKiPj`, `generateMPDO`,
and `CFK`, lines 1660--1665 and 1733--1770. -/
theorem nonempty_physicalSupportRestrictionData_commonWeightAbsorbedBasis
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
    (s : Fin S.basisCount) :
    Nonempty (PhysicalSupportRestrictionData
      (bntSectorProjection hC hρ hη hR s)
      (commonWeightAbsorbedBasisMPOTensor S hWeight s)) := by
  let P := bntSectorProjection hC hρ hη hR s
  let K := commonWeightAbsorbedBasisMPOTensor S hWeight s
  have hBasis : changePhysicalBasis P (S.basisMPOTensor s) =
      S.basisMPOTensor s := by
    simpa [P] using
      changePhysicalBasis_bntSectorProjection_basis hC hρ hη hR s s
  have hSupport : changePhysicalBasis P K = K := by
    change changePhysicalBasis P
        (S.commonWeight hWeight s • S.basisMPOTensor s) =
      S.commonWeight hWeight s • S.basisMPOTensor s
    rw [changePhysicalBasis_smul, hBasis]
  exact exists_physicalSupportRestrictionData P K
    (bntSectorProjection_isOrthogonal hC hρ hη hR s) hSupport
    (commonWeightAbsorbedBasisMPOTensor_isInjective S hWeight hSpan s)

end MPOTensor
