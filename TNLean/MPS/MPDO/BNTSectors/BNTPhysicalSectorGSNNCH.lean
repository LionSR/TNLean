/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTSectors.BNTSectorCommutingFamily
import TNLean.MPS.MPDO.PhysicalSector.PhysicalSectorActiveNeighboring
import TNLean.MPS.FundamentalTheorem.PhysicalSupport.PhysicalSupportBondTransport
import TNLean.MPS.MPDO.BNTSectors.BNTSectorCoefficientPositivity
import TNLean.MPS.MPDO.CommutingForm.GSNNCHSectorRescaling
import TNLean.MPS.Operator.PhysicalSector.NeighboringPreparation

/-!
# Positive bonds from the active physical compression

An ambient physical-sector factorization with positive neighboring operators
has a canonical restriction to the joint physical support of its slices.  The
positive commuting bond constructed on that restriction is supported on every
orthogonal one-site projection which absorbs all physical slices.

**Scope restriction (active physical support compression):** the proofs in
this file first restrict to the joint column supports of the sector factor
families, a finite-dimensional auxiliary construction not made in CPSV16, and
then lift the resulting bond to the printed physical support.  See
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex`.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `AppUkU=rl`, `Appetakhetc`, `PjKiPj`, and
  `generateMPDO`, lines 1383--1450 and 1680--1770.

## GSNNCH form from the five BNT physical-sector identities

The five identities in CPSV16 Appendix C.2 give orthogonally supported positive
commuting bonds for the unweighted BNT representatives. Global MPDO positivity
then makes every fixed-length BNT sector coefficient nonnegative real. Its
positive root, divided by the natural BNT copy number, can be absorbed into the
sector bond. Since GSNNCH data is chosen separately at each chain length, no
copy independence is required.

### References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition `prop3to4`, lines 1786--1796
-/

section

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
1680--1770, and Proposition `3to4`, lines 1570--1594. -/
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
  let A := F.activeFactorSupportData
  let restriction := F.activePhysicalSupportRestrictionData A hK hη
  let G : PhysicalSectorFactorization
      (changePhysicalBasis restriction.inclusionᴴ K) :=
    F.activeRestrictedPhysicalSectorFactorization A
  obtain ⟨data, hdata, hrealizes⟩ :=
    restriction.exists_etaLocalStructureData_lifted_supported_of_physicalSectorFactorization
      G (fun k h ↦
        F.activeRestrictedPhysicalSectorFactorization_neighboringOperator_posSemidef
          A hη k h)
  refine ⟨data, ?_, hrealizes⟩
  let Q := physicalSupportProj K
  have hPQ : P * Q = Q :=
    mul_physicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq
      K P (fun β α ↦ (hSupport β α).1)
  have hQ : IsOrthogonalProjection Q :=
    (Matrix.posSemidef_self_mul_conjTranspose
      (physicalSliceColumns K)).isOrthogonalProjection_supportProj
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
Proposition `prop3to4`, lines 1786--1796. -/
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

end

section

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d : ℕ}

/-- The five identities printed in CPSV16 Proposition `prop3to4` imply the
GSNNCH form without copy independence.

The orthogonality hypothesis is `AppKxKy=0`; the physical-sector
factorizations are `AppUkU=rl`; and each neighboring trace factorization
contains `Appetakhetc`, `Apptralktrrk`, and `AppPsiPhi`. All five hypotheses
are imposed on the raw BNT representatives `S.basisMPOTensor`. The resulting
GSNNCH multiplicities are the natural copy numbers `S.copies`.

Global MPDO positivity is the standing Case II assumption at CPSV16 lines
1626--1629. Positive BNT bond dimensions are stated explicitly because the
bare `SectorDecomposition` type does not store this source-native condition;
without it, algebraic injectivity is vacuous at bond dimension zero.
The simultaneous one-letter span `hSpan` is the standing biCF assumption
imposed at the start of Case II, after passing to the source's common blocking.

The source proof's invocation of Lemma `lemmus` is not used: at each fixed
length the actual coefficient `S.coeff N s` is shown to be nonnegative real
by sitewise compression onto its orthogonal physical support, then its
positive `N`-th root divided by `S.copies s` is absorbed into the supported
commuting bond.

Source: arXiv:1606.00608, Appendix C.2, Case II and equation `biCFK`, lines
1626--1639 and 1666--1676; Proposition `prop3to4`, lines 1786--1796. -/
theorem hasGSNNCHForm_of_bntLayerOrthogonal_of_physicalSectorFactorization
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hMPDO : IsMPDO M)
    (hBasisDim : ∀ s, 0 < S.basisDim s)
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hLayer : IsBNTLayerOrthogonal (fun s ↦ S.basisMPOTensor s))
    (F : (s : Fin S.basisCount) →
      PhysicalSectorFactorization (S.basisMPOTensor s))
    (hTrace : ∀ s,
      PhysicalSectorFactorization.NeighboringTraceFactorization (F s)) :
    HasGSNNCHForm M := by
  let K : (s : Fin S.basisCount) → MPOTensor d (S.basisDim s) :=
    fun s ↦ S.basisMPOTensor s
  have hInjective : ∀ s, (K s).IsInjective := by
    intro s
    change Kraus.IsInjective (K s).toMPSTensor
    dsimp only [K]
    rw [S.basisMPOTensor_toMPSTensor]
    exact hSpan.isInjective_one s
  have hSectorMPDO : ∀ s, IsMPDO (K s) := by
    intro s
    exact (F s).isMPDO_of_neighboringOperator_pos
      (fun k h ↦ (hTrace s).neighboringOperator_pos k h)
  obtain ⟨P, hP, hPorth, hSupport⟩ :=
    exists_pairwise_orthogonal_twoSided_physicalSupport
      K hInjective hSectorMPDO hLayer
  obtain ⟨family⟩ :=
    nonempty_orthogonalCommutingSectorFamily_of_ambientPhysicalSectorFactorization
      K P hP hPorth hInjective hSupport F
      (fun s k h ↦ (hTrace s).neighboringOperator_pos k h)
  intro N hN
  have hsum : mpo M N = ∑ s : Fin S.basisCount,
      S.coeff N s • mpo (K s) N := by
    ext u v
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, K]
    exact S.mpo_eq_sum_coeff_basisMPOTensor M hM (by omega) u v
  have hSectorNe : ∀ s, mpo (K s) N ≠ 0 := by
    intro s hzero
    let : NeZero (S.basisDim s) := ⟨Nat.ne_of_gt (hBasisDim s)⟩
    have hmpv : (MPSTensor.mpv (K s).toMPSTensor :
        MPSTensor.NSiteSpace (d * d) N) ≠ 0 := by
      apply MPSTensor.mpv_ne_zero_of_isNBlkInjective
        (Kraus.isNBlkInjective_one_of_isInjective (hInjective s)) Nat.one_pos
      omega
    apply hmpv
    funext ρ
    let u : Fin N → Fin d := fun n ↦ (ρ n).divNat
    let v : Fin N → Fin d := fun n ↦ (ρ n).modNat
    have hρ : ρ = fun n ↦ finProdFinEquiv (u n, v n) := by
      funext n
      exact (finProdFinEquiv.apply_symm_apply (ρ n)).symm
    rw [hρ, MPSTensor.mpv_toMPSTensor_pairConfig]
    rw [hzero]
    rfl
  obtain ⟨coefficient, hCoefficient, hCoefficientEq⟩ :=
    exists_nonnegative_real_eq_sectorCoefficient_of_orthogonalSupport
      K P hP hPorth hSupport (S.coeff N) (mpo M N)
      (hMPDO N (by omega)) (fun s ↦ hSectorMPDO s N (by omega))
      hSectorNe hsum (by omega)
  have hsumReal : mpo M N = ∑ s : Fin S.basisCount,
      (coefficient s : ℂ) • mpo (K s) N := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro s _
    rw [hCoefficientEq s]
  let data := family.toCoefficientRescaledGSNNCHData
    S.copies S.copies_pos coefficient hCoefficient N hN
  refine ⟨data, 1, by norm_num, ?_⟩
  rw [show ((1 : ℝ) : ℂ) = 1 by norm_num, one_smul]
  change mpo M N =
    (family.toCoefficientRescaledGSNNCHData
      S.copies S.copies_pos coefficient hCoefficient N hN).unnormalizedState
  exact hsumReal.trans
    (family.toCoefficientRescaledGSNNCHData_unnormalizedState
      S.copies S.copies_pos coefficient hCoefficient N hN).symm

end MPOTensor

end
