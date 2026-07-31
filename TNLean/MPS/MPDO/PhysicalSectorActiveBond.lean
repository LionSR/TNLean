/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTSectorCommutingFamily
import TNLean.MPS.MPDO.PhysicalSectorActiveNeighboring
import TNLean.MPS.MPDO.PhysicalSupportBondTransport

/-!
# Positive bonds from the active physical compression

An ambient physical-sector factorization with positive neighboring operators
has a canonical restriction to the joint physical support of its slices.  The
positive commuting bond constructed on that restriction is supported on every
orthogonal one-site projection which absorbs all physical slices.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `AppUkU=rl`, `Appetakhetc`, `PjKiPj`, and
  `generateMPDO`, lines 1383--1450 and 1680--1770.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

namespace PhysicalSectorFactorization

/-- An ambient physical-sector factorization with positive neighboring
operators gives a positive commuting bond supported on every orthogonal
projection which absorbs all physical slices.  Its periodic product is the
original MPO at every length at least two.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl`,
`Appetakhetc`, `PjKiPj`, and `generateMPDO`, lines 1383--1450 and
1680--1770, and Proposition `3to4`, lines 1570--1594.

**Scope restriction (active physical support compression):** The proof first
restricts to the joint column supports of the sector factor families, a
finite-dimensional auxiliary construction not made in CPSV16.  It then lifts
the resulting bond to the printed physical support.  See
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex`. -/
theorem exists_etaLocalStructureData_supported_of_twoSidedPhysicalSlice
    {K : MPOTensor d D} (F : PhysicalSectorFactorization K)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : IsOrthogonalProjection P)
    (hK : K.IsInjective)
    (hSupport : ∀ β α,
      P * physicalSlice K β α = physicalSlice K β α ∧
        physicalSlice K β α * P = physicalSlice K β α)
    (hη : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    ∃ data : EtaLocalStructureData K,
      twoSiteSectorProjection P * data.bondData.bond *
          twoSiteSectorProjection P = data.bondData.bond ∧
      ∀ N (hN : 2 ≤ N),
        mpo K N = (data.bondData.toCommutingFormData hN).product := by
  let W :=
    PhysicalSectorFactorization.ActivePhysicalCompressionWitness.canonical F
  let restriction := W.restrictionData hK hη
  let G := W.factorizationForRestrictionData hK hη
  obtain ⟨data, hdata, hrealizes⟩ :=
    restriction.exists_etaLocalStructureData_lifted_supported_of_physicalSectorFactorization
      G (fun k h ↦ W.neighboringOperator_posSemidef hη k h)
  refine ⟨data, ?_, hrealizes⟩
  let Q := physicalSupportProj K
  have hPQ : P * Q = Q :=
    mul_physicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq
      K P (fun β α ↦ (hSupport β α).1)
  have hQ : IsOrthogonalProjection Q :=
    MPSTensor.isOrthogonalProjection_supportProj
      (physicalSliceColumns K * (physicalSliceColumns K)ᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose (physicalSliceColumns K))
  have hQP : Q * P = Q := by
    have h := congrArg Matrix.conjTranspose hPQ
    rwa [Matrix.conjTranspose_mul, hQ.1.eq, hP.1.eq] at h
  exact twoSiteSectorProjection_supported_of_supported_of_absorbs
    P Q hPQ hQP data.bondData.bond hdata

end PhysicalSectorFactorization

/-- Pairwise orthogonal projections which absorb injective sector tensors
support an orthogonal family of positive commuting bonds whenever the ambient
sector tensors have positive physical-sector factorizations.

Source: arXiv:1606.00608, Appendix C.2, equations `AppKxKy=0`,
`AppUkU=rl`, `Appetakhetc`, `PjKiPj`, and `generateMPDO`, lines
1383--1450 and 1628--1770, Proposition `3to4`, lines 1570--1594, and
Proposition `prop3to4`, lines 1786--1796.

**Scope restriction (active physical support compression):** The proof calls
the preceding active-support construction, which restricts each sector tensor
to the joint column supports of its factor families before constructing the
commuting bond.  CPSV16 does not make this restriction.  See
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex`. -/
theorem nonempty_orthogonalCommutingSectorFamily_of_ambientPhysicalSectorFactorization
    {g : ℕ} {dim : Fin g → ℕ}
    (K : (s : Fin g) → MPOTensor d (dim s))
    (P : Fin g → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ s, IsOrthogonalProjection (P s))
    (hPorth : ∀ {s t}, s ≠ t → P s * P t = 0)
    (hInjective : ∀ s, (K s).IsInjective)
    (hSupport : ∀ s β α,
      P s * physicalSlice (K s) β α = physicalSlice (K s) β α ∧
        physicalSlice (K s) β α * P s = physicalSlice (K s) β α)
    (F : (s : Fin g) → PhysicalSectorFactorization (K s))
    (hη : ∀ s k h, ((F s).neighboringOperator k h).PosSemidef) :
    Nonempty (OrthogonalCommutingSectorFamily K) := by
  classical
  let data : (s : Fin g) → EtaLocalStructureData (K s) :=
    fun s ↦ Classical.choose
      ((F s).exists_etaLocalStructureData_supported_of_twoSidedPhysicalSlice
        (P s) (hP s) (hInjective s) (hSupport s) (hη s))
  have hdata : ∀ s : Fin g,
      twoSiteSectorProjection (P s) * (data s).bondData.bond *
          twoSiteSectorProjection (P s) = (data s).bondData.bond ∧
        ∀ N (hN : 2 ≤ N),
          mpo (K s) N = ((data s).bondData.toCommutingFormData hN).product :=
    fun s ↦ Classical.choose_spec
      ((F s).exists_etaLocalStructureData_supported_of_twoSidedPhysicalSlice
        (P s) (hP s) (hInjective s) (hSupport s) (hη s))
  exact ⟨{
    projection := P
    projection_isOrthogonal := hP
    projection_orthogonal := fun hst ↦ hPorth hst
    bondData := fun s ↦ (data s).bondData
    bond_supported := fun s ↦ (hdata s).1
    realizes_mpo := fun s N hN ↦ (hdata s).2 N hN }⟩

end MPOTensor
