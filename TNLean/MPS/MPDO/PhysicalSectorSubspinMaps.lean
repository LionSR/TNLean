/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.KrausCPTP
import TNLean.MPS.MPDO.PhysicalSectorFactorization

/-!
# Physical-sector subspin maps

This file defines the regrouping and partial trace $\mathcal S_0$, together
with the shift $\mathcal S_2$, directly from a physical-sector factorization
of a simple MPO tensor.  The construction uses only the decomposition

\[
  \mathcal H=\bigoplus_k B_k^L\otimes B_k^R.
\]

In particular, it does not require a quantum-Markov decomposition of a
tripartite state.

## Main declarations

* `s0RegroupEquiv`: the three-site regrouping into the two outer subspins and
  the four middle subspins.
* `s0Map`: the regrouping followed by the partial trace over the four middle
  subspins.
* `s2ShiftEquiv` and `s2Map`: the two-site shift from the regrouped factors
  back to two physical sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, lines 1547 and 1555--1559
-/

open scoped Matrix BigOperators

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The direct sum of the one-site physical-sector indices. -/
abbrev SectorSiteIndex (F : PhysicalSectorFactorization K) :=
  Σ k : Fin F.sectorCount, SectorIndex F k

/-- The direct sum of the two outer subspins retained between sectors $k$
and $h$. -/
abbrev BoundarySubspinIndex (F : PhysicalSectorFactorization K) :=
  Σ kh : Fin F.sectorCount × Fin F.sectorCount, BoundaryIndex F kh.1 kh.2

/-- The four middle subspins traced by $\mathcal S_0$, with the intermediate
sector retained as a direct-sum label. -/
abbrev ThreeSiteMiddleIndex (F : PhysicalSectorFactorization K)
    (k h : Fin F.sectorCount) :=
  Σ l : Fin F.sectorCount, NeighborIndex F k l × NeighborIndex F l h

/-- The direct sum obtained by regrouping three physical sites into the two
outer subspins and the four middle subspins. -/
abbrev S0PreparationIndex (F : PhysicalSectorFactorization K) :=
  Σ kh : Fin F.sectorCount × Fin F.sectorCount,
    BoundaryIndex F kh.1 kh.2 × ThreeSiteMiddleIndex F kh.1 kh.2

/-- The direct sum on which $\mathcal S_2$ acts: two outer subspins together
with the neighboring pair between them. -/
abbrev S2PreparationIndex (F : PhysicalSectorFactorization K) :=
  Σ kh : Fin F.sectorCount × Fin F.sectorCount,
    BoundaryIndex F kh.1 kh.2 × NeighborIndex F kh.1 kh.2

/-- Regroup three physical-sector indices as

$$
((l_k,r_k),((l_l,r_l),(l_h,r_h)))
\longmapsto ((l_k,r_h),(l,(r_k,l_l),(r_l,l_h))).
$$

The first factor consists of the two outer subspins.  The second factor
consists of the four middle subspins that $\mathcal S_0$ traces.

**Local fix (repeated subspin):** the final $2l$ in the source sentence is
read as $3l$, as forced by the source diagram. Documented in
`docs/paper-gaps/cpgsv17_mpdo_s0_trace_subspin_typo.tex`.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
def s0RegroupEquiv (F : PhysicalSectorFactorization K) :
    (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) ≃
      S0PreparationIndex F where
  toFun x := ⟨(x.1.1, x.2.2.1), ((x.1.2.1, x.2.2.2.2),
    ⟨x.2.1.1, ((x.1.2.2, x.2.1.2.1), (x.2.1.2.2, x.2.2.2.1))⟩)⟩
  invFun x := (⟨x.1.1, (x.2.1.1, x.2.2.2.1.1)⟩,
    (⟨x.2.2.1, (x.2.2.2.1.2, x.2.2.2.2.1)⟩,
      ⟨x.1.2, (x.2.2.2.2.2, x.2.1.2)⟩))
  left_inv := by rintro ⟨⟨k, lk, rk⟩, ⟨l, ll, rl⟩, h, lh, rh⟩; rfl
  right_inv := by rintro ⟨⟨k, h⟩, ⟨lk, rh⟩, l, ⟨rk, ll⟩, rl, lh⟩; rfl

/-- The map $\mathcal S_0$: regroup three sites, then trace the four middle
subspins in every orthogonal pair of outer sectors.

**Local fix (repeated subspin):** the final $2l$ in the source sentence is
read as $3l$, as forced by the source diagram. Documented in
`docs/paper-gaps/cpgsv17_mpdo_s0_trace_subspin_typo.tex`.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
noncomputable def s0Map (F : PhysicalSectorFactorization K) :
    Matrix (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F))
        (SectorSiteIndex F × (SectorSiteIndex F × SectorSiteIndex F)) ℂ →ₗ[ℂ]
      Matrix (BoundarySubspinIndex F) (BoundarySubspinIndex F) ℂ :=
  Matrix.controlledPartialTraceRightLM
      (α := fun kh : Fin F.sectorCount × Fin F.sectorCount =>
        BoundaryIndex F kh.1 kh.2)
      (β := fun kh : Fin F.sectorCount × Fin F.sectorCount =>
        ThreeSiteMiddleIndex F kh.1 kh.2) ∘ₗ
    Matrix.equivReindexMap (s0RegroupEquiv F)

/-- The map $\mathcal S_0$ is trace-preserving and completely positive.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
theorem s0Map_isKrausCPTP (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (s0Map F) := by
  simpa [s0Map] using isKrausCPTP_comp
    (Matrix.equivReindexMap_isKrausCPTP (s0RegroupEquiv F))
    Matrix.controlledPartialTraceRightLM_isKrausCPTP

/-- The shift $\mathcal S_2$ regroups an outer pair and its neighboring
subspins into two complete physical sectors:

$$
((l_k,r_h),(r_k,l_h))\longmapsto((l_k,r_k),(l_h,r_h)).
$$

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
def s2ShiftEquiv (F : PhysicalSectorFactorization K) :
    S2PreparationIndex F ≃ (SectorSiteIndex F × SectorSiteIndex F) where
  toFun x := (⟨x.1.1, (x.2.1.1, x.2.2.1)⟩,
    ⟨x.1.2, (x.2.2.2, x.2.1.2)⟩)
  invFun x := ⟨(x.1.1, x.2.1), ((x.1.2.1, x.2.2.2), (x.1.2.2, x.2.2.1))⟩
  left_inv := by rintro ⟨⟨k, h⟩, ⟨lk, rh⟩, rk, lh⟩; rfl
  right_inv := by rintro ⟨⟨k, lk, rk⟩, h, lh, rh⟩; rfl

/-- The global shift $\mathcal S_2$, realized by reindexing matrices along
`s2ShiftEquiv`.

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
def s2Map (F : PhysicalSectorFactorization K) :
    Matrix (S2PreparationIndex F) (S2PreparationIndex F) ℂ →ₗ[ℂ]
      Matrix (SectorSiteIndex F × SectorSiteIndex F)
        (SectorSiteIndex F × SectorSiteIndex F) ℂ :=
  Matrix.equivReindexMap (s2ShiftEquiv F)

/-- The shift $\mathcal S_2$ is trace-preserving and completely positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
theorem s2Map_isKrausCPTP (F : PhysicalSectorFactorization K) :
    IsKrausCPTP (s2Map F) :=
  Matrix.equivReindexMap_isKrausCPTP (s2ShiftEquiv F)

end MPOTensor.PhysicalSectorFactorization
