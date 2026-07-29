/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommonWeightAbsorbedBNTSupport
import TNLean.MPS.MPDO.PhysicalSectorActiveBond

/-!
# GSNNCH form from the five BNT identities

The BNT decomposition of a simple matrix product density operator has the
GSNNCH form when its distinct physical layers are orthogonal and each BNT
representative has the physical-sector factorization and neighboring trace
factorization of Appendix C.2.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Proposition `prop3to4`, lines 1786--1796
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d : ℕ}

/-- The BNT decomposition has the GSNNCH form when the five identities of
CPSV16 Proposition `prop3to4` hold for its representatives.

The orthogonality hypothesis is equation `AppKxKy=0`; the physical-sector
factorizations are equation `AppUkU=rl`; and each neighboring trace
factorization consists of `Appetakhetc`, `Apptralktrrk`, and `AppPsiPhi`.
The copy numbers of the BNT decomposition are the multiplicities of the
resulting GSNNCH sectors.

Source: arXiv:1606.00608, Appendix C.2, Proposition `prop3to4`, lines
1786--1796. -/
theorem hasGSNNCHForm_of_bntLayerOrthogonal_of_physicalSectorFactorization
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

end MPOTensor
