/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorSubspinMaps

/-!
# Physical-sector refinement regroupings

This file defines the two regrouping stages of the refinement channel in
Proposition C.7 directly from a physical-sector factorization.  The first
stage regroups two sites and traces the neighboring subspins.  The last stage
reindexes the prepared outer and middle subspins as three physical sites.

Only the decomposition
\[
  \mathcal H=\bigoplus_k B_k^L\otimes B_k^R
\]
is used.  No quantum-Markov state or neighboring-operator preparation is
assumed here.

## Main declarations

* `t0RegroupEquiv` and `t0Map`: the two-site regrouping and controlled partial
  trace.
* `t2ShiftEquiv` and `t2Map`: the final shift to three physical sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1521--1522 and 1535--1540
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- Regroup two physical sites into the two outer subspins and the neighboring
pair that is traced by \(\mathcal T_0\):
\[
  ((l_k,r_k),(l_h,r_h))\longmapsto((l_k,r_h),(r_k,l_h)).
\]
This equivalence is the inverse of the shift used by \(\mathcal S_2\).

Source: arXiv:1606.00608, Appendix C.2, lines 1521--1522 and 1555--1559. -/
def t0RegroupEquiv (F : PhysicalSectorFactorization K) :
    (SectorSiteIndex F × SectorSiteIndex F) ≃ S2PreparationIndex F :=
  F.s2ShiftEquiv.symm

/-- The map \(\mathcal T_0\): regroup two sites and, in every orthogonal
outer-sector pair, trace the neighboring subspins \(R_k\otimes L_h\).

Source: arXiv:1606.00608, Appendix C.2, line 1522. -/
noncomputable def t0Map (F : PhysicalSectorFactorization K) :
    Matrix (SectorSiteIndex F × SectorSiteIndex F)
        (SectorSiteIndex F × SectorSiteIndex F) ℂ →ₗ[ℂ]
      Matrix (BoundarySubspinIndex F) (BoundarySubspinIndex F) ℂ :=
  Matrix.controlledPartialTraceRightLM
      (α := fun kh : Fin F.sectorCount × Fin F.sectorCount ↦
        BoundaryIndex F kh.1 kh.2)
      (β := fun kh : Fin F.sectorCount × Fin F.sectorCount ↦
        NeighborIndex F kh.1 kh.2) ∘ₗ
    Matrix.equivReindexMap F.t0RegroupEquiv

/-- The map \(\mathcal T_0\) is trace-preserving and completely positive.

Source: arXiv:1606.00608, Appendix C.2, line 1522. -/
theorem t0Map_isKrausCPTP (F : PhysicalSectorFactorization K) :
    IsKrausCPTP F.t0Map := by
  simpa [t0Map] using isKrausCPTP_comp
    (Matrix.equivReindexMap_isKrausCPTP F.t0RegroupEquiv)
    Matrix.controlledPartialTraceRightLM_isKrausCPTP

/-- Regroup the prepared outer and middle subspins as three physical sites:
\[
 ((l_k,r_h),(l,(r_k,l_l),(r_l,l_h)))
 \longmapsto ((l_k,r_k),((l_l,r_l),(l_h,r_h))).
\]
This is the inverse of the regrouping used by \(\mathcal S_0\).

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1540 and 1547. -/
def t2ShiftEquiv (F : PhysicalSectorFactorization K) :
    S0PreparationIndex F ≃
      (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) :=
  F.s0RegroupEquiv.symm

/-- The final shift \(\mathcal T_2\), realized by reindexing along the inverse
three-site regrouping.

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1540. -/
def t2Map (F : PhysicalSectorFactorization K) :
    Matrix (S0PreparationIndex F) (S0PreparationIndex F) ℂ →ₗ[ℂ]
      Matrix (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F))
        (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) ℂ :=
  Matrix.equivReindexMap F.t2ShiftEquiv

/-- The shift \(\mathcal T_2\) is trace-preserving and completely positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1540. -/
theorem t2Map_isKrausCPTP (F : PhysicalSectorFactorization K) :
    IsKrausCPTP F.t2Map :=
  Matrix.equivReindexMap_isKrausCPTP F.t2ShiftEquiv

end MPOTensor.PhysicalSectorFactorization
