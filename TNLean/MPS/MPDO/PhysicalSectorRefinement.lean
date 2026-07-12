/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorOmegaPreparation
import TNLean.MPS.MPDO.PhysicalSectorRefinementRegroupings

/-!
# The physical-sector refinement channel

This file defines the three stages of the refinement channel
\(\mathcal T=\mathcal T_2\mathcal T_1\mathcal T_0\) in Proposition C.7.
The first stage traces the neighboring subspins of two physical sites, the
second adjoins the normalized three-site neighboring operator on each outer
sector pair, and the last reindexes the resulting subspins as three physical
sites.

## Main declarations

* `NeighboringTraceFactorization.t1Map`: the controlled preparation stage.
* `NeighboringTraceFactorization.tMap`: the refinement channel from two sites
  to three sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1522--1545
-/

open scoped Matrix

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D} {F : PhysicalSectorFactorization K}

/-- The map \(\mathcal T_1\) discards coherences between outer-sector pairs
and adjoins the completed three-site neighboring density on each diagonal
summand. On an active pair, this density is
\((a_kb_h)^{-1}\bigoplus_l(\eta_{k,l}\otimes\eta_{l,h})\); the zero-weight
pairs use the trace-preserving completion.

**Local fix (zero-weight quotient):** the inactive branch makes the source map
total without adding a nonzero-weight hypothesis. Documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
noncomputable def NeighboringTraceFactorization.t1Map
    (H : NeighboringTraceFactorization F) :
    Matrix (BoundarySubspinIndex F) (BoundarySubspinIndex F) ℂ →ₗ[ℂ]
      Matrix (S0PreparationIndex F) (S0PreparationIndex F) ℂ :=
  H.completedThreeSiteControlledMap
    (α := fun kh : Fin F.sectorCount × Fin F.sectorCount ↦
      BoundaryIndex F kh.1 kh.2)

/-- The map \(\mathcal T_1\) is trace-preserving and completely positive.

**Local fix (zero-weight quotient):** this theorem includes the completed
inactive branch documented in
`docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`.

Source: arXiv:1606.00608, Appendix C.2, lines 1523--1535. -/
theorem NeighboringTraceFactorization.t1Map_isKrausCPTP
    (H : NeighboringTraceFactorization F) : IsKrausCPTP H.t1Map := by
  exact H.completedThreeSiteControlledMap_isKrausCPTP

/-- The refinement channel
\(\mathcal T=\mathcal T_2\mathcal T_1\mathcal T_0\) from two physical sites
to three physical sites.

Source: arXiv:1606.00608, Appendix C.2, lines 1522--1545. -/
noncomputable def NeighboringTraceFactorization.tMap
    (H : NeighboringTraceFactorization F) :
    Matrix (SectorSiteIndex F × SectorSiteIndex F)
        (SectorSiteIndex F × SectorSiteIndex F) ℂ →ₗ[ℂ]
      Matrix (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F))
        (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) ℂ :=
  F.t2Map ∘ₗ H.t1Map ∘ₗ F.t0Map

/-- The refinement channel \(\mathcal T\) is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1522--1545. -/
theorem NeighboringTraceFactorization.tMap_isKrausCPTP
    (H : NeighboringTraceFactorization F) : IsKrausCPTP H.tMap := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp F.t0Map_isKrausCPTP H.t1Map_isKrausCPTP)
    F.t2Map_isKrausCPTP

end MPOTensor.PhysicalSectorFactorization
