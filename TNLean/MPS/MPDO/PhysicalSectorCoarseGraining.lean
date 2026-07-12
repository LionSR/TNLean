/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.NeighboringPreparation
import TNLean.MPS.MPDO.PhysicalSectorSubspinMaps

/-!
# The physical-sector coarse-graining channel

This file defines the three stages of the coarse-graining channel
\(\mathcal S=\mathcal S_2\mathcal S_1\mathcal S_0\) in Proposition C.7.
The hypotheses are precisely the physical-sector factorization, positivity of
the neighboring operators, and their rank-one trace factorization.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1547--1563
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- The map \(\mathcal S_1\) discards coherences between outer-sector pairs
and adjoins the normalized neighboring density in each diagonal pair.  On a
zero-weight pair it uses an arbitrary density matrix; the neighboring operator
then vanishes, so this choice does not affect the fixed-point identity.

Source: arXiv:1606.00608, Appendix C.2, lines 1548--1555. -/
noncomputable def NeighboringTraceFactorization.s1Map
    (H : NeighboringTraceFactorization F) :
    Matrix (BoundarySubspinIndex F) (BoundarySubspinIndex F) ℂ →ₗ[ℂ]
      Matrix (S2PreparationIndex F) (S2PreparationIndex F) ℂ :=
  H.completedNeighboringControlledMap F.neighborIndex_nonempty
    (α := fun kh : Fin F.sectorCount × Fin F.sectorCount ↦
      BoundaryIndex F kh.1 kh.2)

/-- The map \(\mathcal S_1\) is trace-preserving and completely positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1548--1555. -/
theorem NeighboringTraceFactorization.s1Map_isKrausCPTP
    (H : NeighboringTraceFactorization F) : IsKrausCPTP H.s1Map := by
  exact H.completedNeighboringControlledMap_isKrausCPTP F.neighborIndex_nonempty

/-- The coarse-graining channel
\(\mathcal S=\mathcal S_2\mathcal S_1\mathcal S_0\) from three physical sites
to two physical sites.

Source: arXiv:1606.00608, Appendix C.2, lines 1547--1563. -/
noncomputable def NeighboringTraceFactorization.sMap
    (H : NeighboringTraceFactorization F) :
    Matrix (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F))
        (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) ℂ →ₗ[ℂ]
      Matrix (SectorSiteIndex F × SectorSiteIndex F)
        (SectorSiteIndex F × SectorSiteIndex F) ℂ :=
  F.s2Map ∘ₗ H.s1Map ∘ₗ F.s0Map

/-- The coarse-graining channel \(\mathcal S\) is trace-preserving and
completely positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1547--1563. -/
theorem NeighboringTraceFactorization.sMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) : IsKrausCPTP H.sMap := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp F.s0Map_isKrausCPTP H.s1Map_isKrausCPTP)
    F.s2Map_isKrausCPTP

end MPOTensor.PhysicalSectorFactorization
