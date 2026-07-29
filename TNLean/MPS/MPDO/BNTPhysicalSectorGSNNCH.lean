/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTSectorCoefficientPositivity
import TNLean.MPS.MPDO.CommonWeightAbsorbedBNTSupport
import TNLean.MPS.MPDO.NeighboringPreparation
import TNLean.MPS.MPDO.PhysicalSectorActiveBond

/-!
# GSNNCH form from the five BNT physical-sector identities

The five identities in CPSV16 Appendix C.2 give orthogonally supported positive
commuting bonds for the unweighted BNT representatives. Global MPDO positivity
then makes every fixed-length BNT sector coefficient nonnegative real. Its
positive root, divided by the natural BNT copy number, can be absorbed into the
sector bond. Since GSNNCH data is chosen separately at each chain length, no
copy independence is required.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition `prop3to4`, lines 1786--1796
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d : ℕ}

/-- The earlier common-copy-weight specialization of Proposition `prop3to4`.
The unrestricted theorem below uses the raw BNT representatives instead. -/
theorem hasGSNNCHForm_of_bntLayerOrthogonal_of_physicalSectorFactorization_of_commonWeight
    {D : ℕ} (M : MPOTensor d D)
    (S : MPSTensor.SectorDecomposition (d * d))
    (hM : MPSTensor.SameMPV₂Pos M.toMPSTensor S.toTensor)
    (hWeight : ∀ (s : Fin S.basisCount) (q q' : Fin (S.copies s)),
      S.weight s q = S.weight s q')
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (hLayer : IsBNTLayerOrthogonal
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (F : (s : Fin S.basisCount) → PhysicalSectorFactorization
      (commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (hTrace : ∀ s,
      PhysicalSectorFactorization.NeighboringTraceFactorization (F s)) :
    HasGSNNCHForm M := by
  obtain ⟨P, hP, hPorth, hSupport⟩ :=
    exists_pairwise_orthogonal_twoSided_physicalSupport_commonWeightAbsorbedBasis
      S hWeight hSpan F
        (fun s k h ↦ (hTrace s).neighboringOperator_pos k h) hLayer
  obtain ⟨family⟩ :=
    nonempty_orthogonalCommutingSectorFamily_of_ambientPhysicalSectorFactorization
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s)
      P hP hPorth
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor_isInjective S hWeight hSpan s)
      hSupport F (fun s k h ↦ (hTrace s).neighboringOperator_pos k h)
  exact hasGSNNCHForm_of_commonWeightAbsorbedBasisMPOTensor
    M S hM hWeight family

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

The source proof's invocation of Lemma `lemmus` is not used: at each fixed
length the actual coefficient `S.coeff N s` is shown to be nonnegative real
by sitewise compression onto its orthogonal physical support, then its
positive `N`-th root divided by `S.copies s` is absorbed into the supported
commuting bond.

Source: arXiv:1606.00608, Appendix C.2, Proposition `prop3to4`, lines
1786--1796. -/
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
    change MPSTensor.IsInjective (K s).toMPSTensor
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
    letI : NeZero (S.basisDim s) := ⟨Nat.ne_of_gt (hBasisDim s)⟩
    have hmpv : (MPSTensor.mpv (K s).toMPSTensor :
        MPSTensor.NSiteSpace (d * d) N) ≠ 0 := by
      apply MPSTensor.mpv_ne_zero_of_isNBlkInjective
        (MPSTensor.isNBlkInjective_one_of_isInjective (hInjective s)) Nat.one_pos
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
