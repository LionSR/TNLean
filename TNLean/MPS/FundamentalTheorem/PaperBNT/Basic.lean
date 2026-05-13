/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorDecomposition
import TNLean.MPS.CanonicalForm.Reduction
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Overlap.Basic

/-!
# Paper-faithful BNT canonical form on a `SectorDecomposition`

This module introduces a paper-faithful canonical-form predicate
`IsBNTCanonicalForm` over a `SectorDecomposition d`.  The structure
implements the multi-copy BNT decomposition of CPSV16 §II
(`eq:II_ABasicTensors`, line 286, arXiv:1606.00608) and CPSV21 Definition 4.3
(lines 1846–1850, arXiv:2011.12127) by exposing:

* a **spectral level** `spectralLevel j` with strictly decreasing modulus
  and dominant normalization `‖spectralLevel ⟨0, _⟩‖ = 1`;
* **within-sector unit-modulus phase weights** `phaseWeight j q` with
  `‖phaseWeight j q‖ = 1`, factoring the bare sector weight as
  `P.weight j q = spectralLevel j * phaseWeight j q`;
* **per-block normality data**: each basis block is injective,
  irreducible, left-canonical, and has self-overlap tending to one;
* **eventual linear independence** of basis blocks
  (`HasBNTSectorData`);
* **block distinctness**: distinct basis blocks of equal bond dimension
  are not gauge-phase equivalent.

The resulting MPV decomposition reads
```
mpv P.toTensor σ
  = ∑_j (spectralLevel j)^N · (∑_q (phaseWeight j q)^N) · mpv (P.basis j) σ,
```
where the within-sector unit-modulus power sum `∑_q (phaseWeight j q)^N`
is the CPSV16 §II sector coefficient.  Specializing to one copy per
sector (`P.copies j = 1`) collapses this to a single scalar power; that
specialization is the one captured by the retired one-copy predicate
discussed in issue #1678 (the `C ⊕ -C` example shows that `1 + (-1)^N`
is not a scalar power, which is why the one-copy specialization is
insufficient).

## References

* CPSV16: Cirac--Pérez-García--Schuch--Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points and
  Boundary Theories*, Ann. Phys. **378**, 100 (2017); arXiv:1606.00608.
* CPSV21: Cirac--Pérez-García--Schuch--Verstraete,
  *Matrix product states and projected entangled pair states: Concepts,
  symmetries, theorems*, Rev. Mod. Phys. **93**, 045003 (2021);
  arXiv:2011.12127.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/--
**Paper-faithful BNT canonical form on a sector decomposition.**

Given `P : SectorDecomposition d`, this structure carries the data of a
two-layer multi-copy BNT canonical form (CPSV16
`eq:II_ABasicTensors`, line 286; CPSV21 Definition 4.3,
lines 1846--1850).  See the module docstring for the full mathematical
content; the MPV decomposition reads
```
mpv P.toTensor σ
  = ∑_j (spectralLevel j)^N · (∑_q (phaseWeight j q)^N) · mpv (P.basis j) σ.
```

This predicate is the paper-faithful surface used throughout the FT
chain on multi-copy data.  The retired one-copy predicate discussed in
issue #1678 is *not* a special case of this structure and is not
referenced anywhere here.
-/
structure IsBNTCanonicalForm (P : SectorDecomposition d) where
  /-- Spectral level: one nonzero complex number per BNT sector. -/
  spectralLevel : Fin P.basisCount → ℂ
  /-- The spectral level is everywhere nonzero. -/
  spectralLevel_ne_zero : ∀ j, spectralLevel j ≠ 0
  /-- Spectral-level moduli are strictly decreasing in `j`. -/
  spectralLevel_strict_anti :
    StrictAnti (fun j : Fin P.basisCount => ‖spectralLevel j‖)
  /-- **Dominant normalization** of the spectral level. -/
  spectralLevel_dom_norm_one :
    ∀ h : 0 < P.basisCount, ‖spectralLevel ⟨0, h⟩‖ = 1
  /-- Within-sector unit-modulus phase weights `ν_{j,q}`. -/
  phaseWeight : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ
  /-- Every within-sector phase weight has unit modulus. -/
  phaseWeight_norm_one : ∀ j q, ‖phaseWeight j q‖ = 1
  /-- Factorization `μ_{j,q} = λ_j · ν_{j,q}` of the sector weights. -/
  weight_factor : ∀ j q, P.weight j q = spectralLevel j * phaseWeight j q
  /-- Per-block injectivity of the basis. -/
  basis_injective : ∀ j, IsInjective (P.basis j)
  /-- Per-block irreducibility of the basis. -/
  basis_irreducible : ∀ j, IsIrreducibleTensor (P.basis j)
  /-- Per-block left-canonical form of the basis. -/
  basis_left_canonical : ∀ j, IsLeftCanonical (P.basis j)
  /-- Per-block normalized self-overlap. -/
  basis_normalized_self_overlap : ∀ j,
    Tendsto (fun N : ℕ => mpvOverlap (d := d) (P.basis j) (P.basis j) N)
      atTop (𝓝 1)
  /-- Eventual linear independence of basis blocks (CPSV21 Def. 4.3). -/
  bnt_data : HasBNTSectorData P
  /-- **Block distinctness**: distinct equal-dimension basis blocks are
  not gauge-phase equivalent.  This matches the convention used by
  `BlocksNotGaugePhaseEquiv` in `TNLean/MPS/BNT/Construction.lean`. -/
  basis_distinct : ∀ j k : Fin P.basisCount, j ≠ k →
    ∀ h : P.basisDim j = P.basisDim k,
      ¬ GaugePhaseEquiv
          (cast (congr_arg (MPSTensor d) h) (P.basis j)) (P.basis k)

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- **All spectral-level moduli are bounded by `1`.**

Combines `spectralLevel_dom_norm_one` with `spectralLevel_strict_anti`:
the dominant block has unit modulus and every other block has strictly
smaller modulus, so every modulus is at most `1`. -/
theorem spectralLevel_norm_le_one (h : IsBNTCanonicalForm P)
    (j : Fin P.basisCount) : ‖h.spectralLevel j‖ ≤ 1 := by
  have hpos : 0 < P.basisCount := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hdom : ‖h.spectralLevel ⟨0, hpos⟩‖ = 1 :=
    h.spectralLevel_dom_norm_one hpos
  have hle : (⟨0, hpos⟩ : Fin P.basisCount) ≤ j :=
    Fin.mk_le_of_le_val (Nat.zero_le _)
  have hanti : ‖h.spectralLevel j‖ ≤ ‖h.spectralLevel ⟨0, hpos⟩‖ :=
    h.spectralLevel_strict_anti.antitone hle
  rw [hdom] at hanti
  exact hanti

/-- Phase weights are nonzero (immediate from `phaseWeight_norm_one`). -/
theorem phaseWeight_ne_zero (h : IsBNTCanonicalForm P)
    (j : Fin P.basisCount) (q : Fin (P.copies j)) :
    h.phaseWeight j q ≠ 0 := by
  have hnorm := h.phaseWeight_norm_one j q
  intro hzero
  rw [hzero, norm_zero] at hnorm
  exact one_ne_zero hnorm.symm

/-- Sector weights are nonzero, re-derivable from
`spectralLevel_ne_zero` and `phaseWeight_norm_one`. -/
theorem weight_ne_zero_from_factor (h : IsBNTCanonicalForm P)
    (j : Fin P.basisCount) (q : Fin (P.copies j)) :
    P.weight j q ≠ 0 := by
  rw [h.weight_factor j q]
  exact mul_ne_zero (h.spectralLevel_ne_zero j) (h.phaseWeight_ne_zero j q)

/-- **Sector coefficient identity.**

The sector coefficient `coeff N j = ∑_q (μ_{j,q})^N` factors as the
product of the `N`-th power of the spectral level and the within-sector
unit-modulus power sum `∑_q (ν_{j,q})^N`. -/
theorem coeff_eq_pow_unit_sum (h : IsBNTCanonicalForm P)
    (N : ℕ) (j : Fin P.basisCount) :
    P.coeff N j =
      (h.spectralLevel j) ^ N *
        ∑ q : Fin (P.copies j), (h.phaseWeight j q) ^ N := by
  classical
  unfold SectorDecomposition.coeff SectorWeightData.coeff
  calc
    ∑ q : Fin (P.copies j), (P.weight j q) ^ N
        = ∑ q : Fin (P.copies j),
            (h.spectralLevel j * h.phaseWeight j q) ^ N := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [h.weight_factor j q]
    _ = ∑ q : Fin (P.copies j),
          (h.spectralLevel j) ^ N * (h.phaseWeight j q) ^ N := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [mul_pow]
    _ = (h.spectralLevel j) ^ N *
          ∑ q : Fin (P.copies j), (h.phaseWeight j q) ^ N := by
          rw [← Finset.mul_sum]

end IsBNTCanonicalForm

end MPSTensor
