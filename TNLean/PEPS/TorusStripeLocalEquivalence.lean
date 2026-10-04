/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusSimplyConnectedPhysicalDensity
import TNLean.PEPS.TorusRectangleRealization

/-!
# Unitary equivalence on two width-one torus stripes

The complement of the coordinate-zero horizontal and vertical stripes is a
nonwrapping rectangle. Its actual closed-cell realization is simply connected,
and its induced occupied graph is connected. Consequently every two normalized
coherent physical closure states are related by a unitary on those stripes.

**Scope restriction (regular native torus):** Both periods are at least three.
The statements concern the actual coherent closure vectors. The identification
of this family with a parent-Hamiltonian ground space is a separate result.
Source: SCP10, arXiv:1001.3807, Theorem 6.7, lines 1995–2015;
see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height

/-- The complement of the nonwrapping rectangle consists of one horizontal
and one vertical stripe, each of width one. Source: SCP10, Theorem 6.7,
lines 1995–2015. -/
theorem mem_compl_torusStripeInterior_iff_coordinate_zero (v : X) :
    v ∈ Finset.univ \
      torusContiguousRectangle (width := width) (height := height)
      1 1 (width - 1) (height - 1) ↔ v.1 = 0 ∨ v.2 = 0 := by
  have hw : 1 + (width - 1) = width := by have := Fact.out (p := 2 < width); omega
  have hh : 1 + (height - 1) = height := by have := Fact.out (p := 2 < height); omega
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_torusContiguousRectangle,
    hw, hh, ZMod.val_lt, and_true]
  simp only [not_and_or, not_le, Nat.lt_one_iff, ZMod.val_eq_zero]

/-- A unitary supported on the two coordinate-zero stripes relates any two
normalized coherent physical closure states.
Source: SCP10, Theorem 6.7, lines 1995–2015. -/
theorem IsGIsometric.torusClosureSuperpositionCut_stripe_local_equivalence
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGIsometric (torusLegRep (leftRegularMatrix G)) (siteMap a))
    {I J : Type*} [Fintype I] [Fintype J]
    (pairs : I → G × G) (pairs' : J → G × G)
    (hcomm : ∀ i, Commute (pairs i).1 (pairs i).2)
    (hcomm' : ∀ j, Commute (pairs' j).1 (pairs' j).2)
    (μ : I → ℂ) (μ' : J → ℂ)
    (hne : torusClosureSuperpositionCut a pairs μ
      (torusContiguousRectangle (width := width) (height := height)
        1 1 (width - 1) (height - 1)) ≠ 0)
    (hne' : torusClosureSuperpositionCut a pairs' μ'
      (torusContiguousRectangle (width := width) (height := height)
        1 1 (width - 1) (height - 1)) ≠ 0) :
    let R := torusContiguousRectangle (width := width) (height := height)
      1 1 (width - 1) (height - 1)
    let A : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => torusClosureSuperpositionCut a pairs μ R (σ, τ)
    let B : Matrix (RegionPhysicalConfig (d := d) R)
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ :=
      fun σ τ => torusClosureSuperpositionCut a pairs' μ' R (σ, τ)
    ∃ U : Matrix.unitaryGroup (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ,
      normalizedPureCutMatrix B = normalizedPureCutMatrix A *
        (U : Matrix (RegionPhysicalConfig (d := d) (Finset.univ \ R))
          (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ).transpose := by
  have hw := Fact.out (p := 2 < width)
  have hh := Fact.out (p := 2 < height)
  have hR := torusGraph_rectangle_connected (width := width) (height := height)
    1 1 (width - 1) (height - 1)
    (by omega) (by omega) (by omega) (by omega)
  have hSC := isSimplyConnected_torusRegionRealization_rectangle
    (width := width) (height := height) 1 1 (width - 1) (height - 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact (ha.torusPhysicalCut_local_equivalence_of_isSimplyConnected
    _ hR hSC pairs pairs' hcomm hcomm' μ μ' hne hne').2

end TNLean.PEPS
