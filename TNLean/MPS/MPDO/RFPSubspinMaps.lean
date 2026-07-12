/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.EtaPreparation

/-!
# Subspin regrouping and shifts for the MPDO fixed-point maps

This file gives the concrete dependent equivalences underlying the partial
traces $\mathcal T_0$, $\mathcal S_0$ and the shifts $\mathcal T_2$,
$\mathcal S_2$ in arXiv:1606.00608, Appendix C.2, lines 1521--1522,
1535--1540, 1547, and 1555--1559.

The retained outer subspins in sectors $k,h$ have index
$B_k^L\times B_h^R$. The complementary factors are precisely the index space
of $\eta_{k,h}$ for two sites and of one summand of $\Omega_{k,h}$ for three
sites. No equality between the left and right sector dimensions is required:
the equivalences only reorder existing factors.

## Main declarations

* `t0RegroupEquiv` and `s2ShiftEquiv`: the mutually inverse two-site
  regrouping and shift.
* `s0RegroupEquiv` and `t2ShiftEquiv`: the mutually inverse three-site
  regrouping and shift.
* `t0Map` and `s0Map`: the regroupings followed by their dependent controlled
  partial traces.
* `t2Map` and `s2Map`: the two global shift channels.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.ExplicitEtaOperators

variable {dA dB dC : ℕ}
variable {rhoABC : Matrix (Fin dA × Fin dB × Fin dC)
  (Fin dA × Fin dB × Fin dC) ℂ}
variable {hη : EtaStructure rhoABC}

/-- The physical left-right index within one Hayashi sector. -/
abbrev PhysicalSectorIndex (hη : EtaStructure rhoABC) (k : Fin hη.m) :=
  Fin (hη.dL k) × Fin (hη.dR k)

/-- The two outer subspins retained after tracing between sectors $k$ and
$h$. -/
abbrev OuterSubspinIndex (hη : EtaStructure rhoABC) (k h : Fin hη.m) :=
  Fin (hη.dL k) × Fin (hη.dR h)

/-- The neighboring subspins carrying $\eta_{k,h}$. -/
abbrev NeighborSubspinIndex (hη : EtaStructure rhoABC) (k h : Fin hη.m) :=
  Fin (hη.dR k) × Fin (hη.dL h)

/-- Regroup two sector indices into the outer subspins and the neighboring
subspins to be traced:

$$
((l_k,r_k),(l_h,r_h))\longmapsto((l_k,r_h),(r_k,l_h)).
$$

This is the factor regrouping preceding $\mathcal T_0$ in
arXiv:1606.00608, Appendix C.2, lines 1521--1522. -/
def twoSiteTraceRegroupEquiv (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    (PhysicalSectorIndex hη k × PhysicalSectorIndex hη h) ≃
      (OuterSubspinIndex hη k h × NeighborSubspinIndex hη k h) where
  toFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  invFun x := ((x.1.1, x.2.1), (x.2.2, x.1.2))
  left_inv := by rintro ⟨⟨lk, rk⟩, lh, rh⟩; rfl
  right_inv := by rintro ⟨⟨lk, rh⟩, rk, lh⟩; rfl

/-- Regroup three sector indices into the outer subspins and the four middle
subspins to be traced:

$$
((l_k,r_k),((l_l,r_l),(l_h,r_h)))
\longmapsto ((l_k,r_h),((r_k,l_l),(r_l,l_h))).
$$

This is the factor regrouping preceding $\mathcal S_0$ in
arXiv:1606.00608, Appendix C.2, line 1547, and in the corresponding source
diagram. The repeated ``$2l$'' in the prose at line 1547 is read as ``$3l$'';
see `docs/paper-gaps/cpgsv17_mpdo_s0_trace_subspin_typo.tex`. -/
def threeSiteTraceRegroupEquiv (hη : EtaStructure rhoABC) (k l h : Fin hη.m) :
    (PhysicalSectorIndex hη k ×
        (PhysicalSectorIndex hη l × PhysicalSectorIndex hη h)) ≃
      (OuterSubspinIndex hη k h ×
        (NeighborSubspinIndex hη k l × NeighborSubspinIndex hη l h)) where
  toFun x := ((x.1.1, x.2.2.2), ((x.1.2, x.2.1.1), (x.2.1.2, x.2.2.1)))
  invFun x := ((x.1.1, x.2.1.1), ((x.2.1.2, x.2.2.1), (x.2.2.2, x.1.2)))
  left_inv := by rintro ⟨⟨lk, rk⟩, ⟨ll, rl⟩, lh, rh⟩; rfl
  right_inv := by rintro ⟨⟨lk, rh⟩, ⟨rk, ll⟩, rl, lh⟩; rfl

/-- The two-site shift which turns an outer pair together with
$\eta_{k,h}$ into two complete physical sectors:

$$
((l_k,r_h),(r_k,l_h))\longmapsto((l_k,r_k),(l_h,r_h)).
$$

This is $\mathcal S_2$ in arXiv:1606.00608, Appendix C.2,
lines 1555--1559. -/
def etaShiftEquiv (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    (OuterSubspinIndex hη k h × NeighborSubspinIndex hη k h) ≃
      (PhysicalSectorIndex hη k × PhysicalSectorIndex hη h) :=
  (twoSiteTraceRegroupEquiv hη k h).symm

/-- The three-site shift which turns an outer pair together with one summand
of $\Omega_{k,h}$ into three complete physical sectors:

$$
((l_k,r_h),((r_k,l_l),(r_l,l_h)))
\longmapsto ((l_k,r_k),((l_l,r_l),(l_h,r_h))).
$$

This is $\mathcal T_2$ in arXiv:1606.00608, Appendix C.2,
lines 1535--1540. -/
def omegaShiftEquiv (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    (OuterSubspinIndex hη k h × OmegaIndex (hη := hη) k h) ≃
      (Σ l : Fin hη.m,
        PhysicalSectorIndex hη k ×
          (PhysicalSectorIndex hη l × PhysicalSectorIndex hη h)) where
  toFun x := ⟨x.2.1,
    ((x.1.1, x.2.2.1.1), ((x.2.2.1.2, x.2.2.2.1), (x.2.2.2.2, x.1.2)))⟩
  invFun x := ((x.2.1.1, x.2.2.2.2),
    ⟨x.1, ((x.2.1.2, x.2.2.1.1), (x.2.2.1.2, x.2.2.2.1))⟩)
  left_inv := by rintro ⟨⟨lk, rh⟩, l, ⟨rk, ll⟩, rl, lh⟩; rfl
  right_inv := by rintro ⟨l, ⟨⟨lk, rk⟩, ⟨ll, rl⟩, lh, rh⟩⟩; rfl

/-! ## Global dependent-sum equivalences -/

/-- The full one-site direct sum of physical sector indices. -/
abbrev SectorSiteIndex (hη : EtaStructure rhoABC) :=
  Σ k : Fin hη.m, PhysicalSectorIndex hη k

/-- The full direct sum of retained outer-subspin indices. -/
abbrev BoundarySubspinIndex (hη : EtaStructure rhoABC) :=
  Σ kh : Fin hη.m × Fin hη.m, OuterSubspinIndex hη kh.1 kh.2

/-- The full direct sum obtained after the two-site regrouping for
$\mathcal T_0$, equivalently the input index of the $\mathcal S_2$ shift. -/
abbrev EtaPreparationIndex (hη : EtaStructure rhoABC) :=
  Σ kh : Fin hη.m × Fin hη.m,
    OuterSubspinIndex hη kh.1 kh.2 × NeighborSubspinIndex hη kh.1 kh.2

/-- The full direct sum obtained after the three-site regrouping for
$\mathcal S_0$, equivalently the input index of the $\mathcal T_2$ shift. -/
abbrev OmegaPreparationIndex (hη : EtaStructure rhoABC) :=
  Σ kh : Fin hη.m × Fin hη.m,
    OuterSubspinIndex hη kh.1 kh.2 × OmegaIndex (hη := hη) kh.1 kh.2

/-- The global two-site regrouping into retained and traced subspins. It is
the dependent direct-sum form of `twoSiteTraceRegroupEquiv`.

Source: arXiv:1606.00608, Appendix C.2, lines 1521--1522 and 1555--1559. -/
def t0RegroupEquiv (hη : EtaStructure rhoABC) :
    (SectorSiteIndex hη × SectorSiteIndex hη) ≃ EtaPreparationIndex hη where
  toFun x := ⟨(x.1.1, x.2.1), ((x.1.2.1, x.2.2.2), (x.1.2.2, x.2.2.1))⟩
  invFun x := (⟨x.1.1, (x.2.1.1, x.2.2.1)⟩,
    ⟨x.1.2, (x.2.2.2, x.2.1.2)⟩)
  left_inv := by rintro ⟨⟨k, lk, rk⟩, h, lh, rh⟩; rfl
  right_inv := by rintro ⟨⟨k, h⟩, ⟨lk, rh⟩, rk, lh⟩; rfl

/-- The global two-site shift $\mathcal S_2$ is the inverse of the regrouping
used by $\mathcal T_0$.

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
def s2ShiftEquiv (hη : EtaStructure rhoABC) :
    EtaPreparationIndex hη ≃ (SectorSiteIndex hη × SectorSiteIndex hη) :=
  (t0RegroupEquiv hη).symm

/-- The global three-site regrouping into retained and traced subspins. It is
the dependent direct-sum form of `threeSiteTraceRegroupEquiv`.

**Local fix (repeated subspin):** the final $2l$ in the source sentence is
read as $3l$, as forced by the source diagram. Documented in
`docs/paper-gaps/cpgsv17_mpdo_s0_trace_subspin_typo.tex`.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
def s0RegroupEquiv (hη : EtaStructure rhoABC) :
    (SectorSiteIndex hη × (SectorSiteIndex hη × SectorSiteIndex hη)) ≃
      OmegaPreparationIndex hη where
  toFun x := ⟨(x.1.1, x.2.2.1), ((x.1.2.1, x.2.2.2.2),
    ⟨x.2.1.1, ((x.1.2.2, x.2.1.2.1), (x.2.1.2.2, x.2.2.2.1))⟩)⟩
  invFun x := (⟨x.1.1, (x.2.1.1, x.2.2.2.1.1)⟩,
    (⟨x.2.2.1, (x.2.2.2.1.2, x.2.2.2.2.1)⟩,
      ⟨x.1.2, (x.2.2.2.2.2, x.2.1.2)⟩))
  left_inv := by rintro ⟨⟨k, lk, rk⟩, ⟨l, ll, rl⟩, h, lh, rh⟩; rfl
  right_inv := by rintro ⟨⟨k, h⟩, ⟨lk, rh⟩, l, ⟨rk, ll⟩, rl, lh⟩; rfl

/-- The global three-site shift $\mathcal T_2$ is the inverse of the
regrouping used by $\mathcal S_0$.

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1540. -/
def t2ShiftEquiv (hη : EtaStructure rhoABC) :
    OmegaPreparationIndex hη ≃
      (SectorSiteIndex hη × (SectorSiteIndex hη × SectorSiteIndex hη)) :=
  (s0RegroupEquiv hη).symm

/-! ## The four channels -/

/-- The global map $\mathcal T_0$: regroup two sites into the retained outer
subspins and the neighboring inner subspins, then trace the inner factors in
each orthogonal sector pair.

Source: arXiv:1606.00608, Appendix C.2, lines 1521--1522. -/
noncomputable def t0Map (hη : EtaStructure rhoABC) :
    Matrix (SectorSiteIndex hη × SectorSiteIndex hη)
        (SectorSiteIndex hη × SectorSiteIndex hη) ℂ →ₗ[ℂ]
      Matrix (BoundarySubspinIndex hη) (BoundarySubspinIndex hη) ℂ :=
  Matrix.controlledPartialTraceRightLM
      (α := fun kh : Fin hη.m × Fin hη.m => OuterSubspinIndex hη kh.1 kh.2)
      (β := fun kh : Fin hη.m × Fin hη.m => NeighborSubspinIndex hη kh.1 kh.2) ∘ₗ
    Matrix.equivReindexMap (t0RegroupEquiv hη)

/-- The global map $\mathcal T_0$ is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1521--1522. -/
theorem t0Map_isKrausCPTP (hη : EtaStructure rhoABC) :
    IsKrausCPTP (t0Map hη) := by
  simpa [t0Map] using isKrausCPTP_comp
    (Matrix.equivReindexMap_isKrausCPTP (t0RegroupEquiv hη))
    Matrix.controlledPartialTraceRightLM_isKrausCPTP

/-- The global map $\mathcal S_0$: regroup three sites into the retained outer
subspins and the two neighboring inner pairs, then trace the inner factors in
each orthogonal outer-sector pair.

**Local fix (repeated subspin):** the final $2l$ in the source sentence is
read as $3l$, as forced by the source diagram. Documented in
`docs/paper-gaps/cpgsv17_mpdo_s0_trace_subspin_typo.tex`.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
noncomputable def s0Map (hη : EtaStructure rhoABC) :
    Matrix (SectorSiteIndex hη × (SectorSiteIndex hη × SectorSiteIndex hη))
        (SectorSiteIndex hη × (SectorSiteIndex hη × SectorSiteIndex hη)) ℂ →ₗ[ℂ]
      Matrix (BoundarySubspinIndex hη) (BoundarySubspinIndex hη) ℂ :=
  Matrix.controlledPartialTraceRightLM
      (α := fun kh : Fin hη.m × Fin hη.m => OuterSubspinIndex hη kh.1 kh.2)
      (β := fun kh : Fin hη.m × Fin hη.m => OmegaIndex (hη := hη) kh.1 kh.2) ∘ₗ
    Matrix.equivReindexMap (s0RegroupEquiv hη)

/-- The global map $\mathcal S_0$ is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
theorem s0Map_isKrausCPTP (hη : EtaStructure rhoABC) :
    IsKrausCPTP (s0Map hη) := by
  simpa [s0Map] using isKrausCPTP_comp
    (Matrix.equivReindexMap_isKrausCPTP (s0RegroupEquiv hη))
    Matrix.controlledPartialTraceRightLM_isKrausCPTP

/-- The global shift $\mathcal S_2$, realized by reindexing along the inverse
of the two-site regrouping.

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
def s2Map (hη : EtaStructure rhoABC) :
    Matrix (EtaPreparationIndex hη) (EtaPreparationIndex hη) ℂ →ₗ[ℂ]
      Matrix (SectorSiteIndex hη × SectorSiteIndex hη)
        (SectorSiteIndex hη × SectorSiteIndex hη) ℂ :=
  Matrix.equivReindexMap (s2ShiftEquiv hη)

/-- The global shift $\mathcal S_2$ is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
theorem s2Map_isKrausCPTP (hη : EtaStructure rhoABC) :
    IsKrausCPTP (s2Map hη) :=
  Matrix.equivReindexMap_isKrausCPTP (s2ShiftEquiv hη)

/-- The global shift $\mathcal T_2$, realized by reindexing along the inverse
of the three-site regrouping.

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1540. -/
def t2Map (hη : EtaStructure rhoABC) :
    Matrix (OmegaPreparationIndex hη) (OmegaPreparationIndex hη) ℂ →ₗ[ℂ]
      Matrix (SectorSiteIndex hη × (SectorSiteIndex hη × SectorSiteIndex hη))
        (SectorSiteIndex hη × (SectorSiteIndex hη × SectorSiteIndex hη)) ℂ :=
  Matrix.equivReindexMap (t2ShiftEquiv hη)

/-- The global shift $\mathcal T_2$ is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1540. -/
theorem t2Map_isKrausCPTP (hη : EtaStructure rhoABC) :
    IsKrausCPTP (t2Map hη) :=
  Matrix.equivReindexMap_isKrausCPTP (t2ShiftEquiv hη)

/-! ### Fiberwise forms -/

/-- The sectorwise map $\mathcal T_0$: regroup two physical sectors, then
trace the neighboring subspins $B_k^R\otimes B_h^L$.

Source: arXiv:1606.00608, Appendix C.2, lines 1521--1522. -/
noncomputable def t0SectorMap (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    Matrix (PhysicalSectorIndex hη k × PhysicalSectorIndex hη h)
        (PhysicalSectorIndex hη k × PhysicalSectorIndex hη h) ℂ →ₗ[ℂ]
      Matrix (OuterSubspinIndex hη k h) (OuterSubspinIndex hη k h) ℂ :=
  Matrix.partialTraceRightLM ∘ₗ Matrix.equivReindexMap (twoSiteTraceRegroupEquiv hη k h)

/-- The sectorwise map $\mathcal T_0$ is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1521--1522. -/
theorem t0SectorMap_isKrausCPTP (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    IsKrausCPTP (t0SectorMap hη k h) :=
  isKrausCPTP_comp
    (Matrix.equivReindexMap_isKrausCPTP (twoSiteTraceRegroupEquiv hη k h))
    Matrix.partialTraceRightLM_isKrausCPTP

/-- The sectorwise map $\mathcal S_0$: regroup three physical sectors, then
trace the four middle subspins.

**Local fix (repeated subspin):** the source prose lists $2l$ twice. The
diagram and the required outer factors show that the last traced subspin is
$3l$. Documented in
`docs/paper-gaps/cpgsv17_mpdo_s0_trace_subspin_typo.tex`.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
noncomputable def s0SectorMap (hη : EtaStructure rhoABC) (k l h : Fin hη.m) :
    Matrix (PhysicalSectorIndex hη k ×
        (PhysicalSectorIndex hη l × PhysicalSectorIndex hη h))
        (PhysicalSectorIndex hη k ×
          (PhysicalSectorIndex hη l × PhysicalSectorIndex hη h)) ℂ →ₗ[ℂ]
      Matrix (OuterSubspinIndex hη k h) (OuterSubspinIndex hη k h) ℂ :=
  Matrix.partialTraceRightLM ∘ₗ
    Matrix.equivReindexMap (threeSiteTraceRegroupEquiv hη k l h)

/-- The sectorwise map $\mathcal S_0$ is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, line 1547. -/
theorem s0SectorMap_isKrausCPTP (hη : EtaStructure rhoABC) (k l h : Fin hη.m) :
    IsKrausCPTP (s0SectorMap hη k l h) :=
  isKrausCPTP_comp
    (Matrix.equivReindexMap_isKrausCPTP (threeSiteTraceRegroupEquiv hη k l h))
    Matrix.partialTraceRightLM_isKrausCPTP

/-- The sectorwise shift $\mathcal S_2$, realized as matrix reindexing along
`etaShiftEquiv`.

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
def s2SectorMap (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    Matrix (OuterSubspinIndex hη k h × NeighborSubspinIndex hη k h)
        (OuterSubspinIndex hη k h × NeighborSubspinIndex hη k h) ℂ →ₗ[ℂ]
      Matrix (PhysicalSectorIndex hη k × PhysicalSectorIndex hη h)
        (PhysicalSectorIndex hη k × PhysicalSectorIndex hη h) ℂ :=
  Matrix.equivReindexMap (etaShiftEquiv hη k h)

/-- The sectorwise shift $\mathcal S_2$ is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1555--1559. -/
theorem s2SectorMap_isKrausCPTP (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    IsKrausCPTP (s2SectorMap hη k h) :=
  Matrix.equivReindexMap_isKrausCPTP (etaShiftEquiv hη k h)

/-- The sectorwise shift $\mathcal T_2$, realized as matrix reindexing along
`omegaShiftEquiv`.

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1540. -/
def t2SectorMap (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    Matrix (OuterSubspinIndex hη k h × OmegaIndex (hη := hη) k h)
        (OuterSubspinIndex hη k h × OmegaIndex (hη := hη) k h) ℂ →ₗ[ℂ]
      Matrix (Σ l : Fin hη.m,
          PhysicalSectorIndex hη k ×
            (PhysicalSectorIndex hη l × PhysicalSectorIndex hη h))
        (Σ l : Fin hη.m,
          PhysicalSectorIndex hη k ×
            (PhysicalSectorIndex hη l × PhysicalSectorIndex hη h)) ℂ :=
  Matrix.equivReindexMap (omegaShiftEquiv hη k h)

/-- The sectorwise shift $\mathcal T_2$ is trace-preserving and completely
positive.

Source: arXiv:1606.00608, Appendix C.2, lines 1535--1540. -/
theorem t2SectorMap_isKrausCPTP (hη : EtaStructure rhoABC) (k h : Fin hη.m) :
    IsKrausCPTP (t2SectorMap hη k h) :=
  Matrix.equivReindexMap_isKrausCPTP (omegaShiftEquiv hη k h)

end MPOTensor.ExplicitEtaOperators
