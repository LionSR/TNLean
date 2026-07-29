/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTLayerOrthogonality
import TNLean.MPS.MPDO.PhysicalSupportRestriction

/-!
# Physical supports for common-weight-absorbed BNT representatives

This file specializes the generic support theorem for orthogonal BNT layers to the
common-weight-absorbed representatives of a sector decomposition.  One-site spanning supplies
injectivity, while positivity of the neighboring operators supplies the MPDO condition through
the given physical-sector factorizations.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `CFK`, `AppUkU=rl`, `Appetakhetc`, `AppKxKy=0`, and `PjKiPj`,
  lines 1383--1450 and 1634--1691
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d : ℕ}

/-- Common-weight-absorbed BNT representatives with positive neighboring operators and
orthogonal vertical layers have pairwise orthogonal two-sided physical support projections.

This combines the standing one-site spanning condition with the local physical-sector
factorization and pointwise positivity of its neighboring operators; no trace factorization is
required.  It constructs the sector supports but does not assert that their sum is the identity.

Source: arXiv:1606.00608, Appendix C.2, equations `CFK`, `AppUkU=rl`, `Appetakhetc`,
`AppKxKy=0`, and `PjKiPj`, lines 1383--1450 and 1634--1691. -/
theorem exists_pairwise_orthogonal_twoSided_physicalSupport_commonWeightAbsorbedBasis
    (S : MPSTensor.SectorDecomposition (d * d))
    (hWeight : ∀ (j : Fin S.basisCount) (q q' : Fin (S.copies j)),
      S.weight j q = S.weight j q')
    (hSpan : MPSTensor.WordTupleSpanTop S.basis 1)
    (F : (s : Fin S.basisCount) → PhysicalSectorFactorization
      (commonWeightAbsorbedBasisMPOTensor S hWeight s))
    (hNeighbor : ∀ s q h, ((F s).neighboringOperator q h).PosSemidef)
    (hLayer : IsBNTLayerOrthogonal
      (fun s ↦ commonWeightAbsorbedBasisMPOTensor S hWeight s)) :
    ∃ P : Fin S.basisCount → Matrix (Fin d) (Fin d) ℂ,
      (∀ s, IsOrthogonalProjection (P s)) ∧
      (∀ {s t}, s ≠ t → P s * P t = 0) ∧
      (∀ s (β α : Fin (S.basisDim s)),
        P s * physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α =
            physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α ∧
          physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α * P s =
            physicalSlice (commonWeightAbsorbedBasisMPOTensor S hWeight s) β α) := by
  apply exists_pairwise_orthogonal_twoSided_physicalSupport
  · exact fun s ↦ commonWeightAbsorbedBasisMPOTensor_isInjective S hWeight hSpan s
  · exact fun s ↦ (F s).isMPDO_of_neighboringOperator_pos (hNeighbor s)
  · exact hLayer

end MPOTensor
