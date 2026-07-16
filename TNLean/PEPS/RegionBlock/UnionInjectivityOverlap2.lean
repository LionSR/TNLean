/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap

/-!
# The overlapping union lemma: the crossing collapse and the closure

This file closes the overlapping union-of-injective-regions lemma of the normal PEPS
Fundamental Theorem (arXiv:1804.04964, Section 3, Lemma `injective_union`, lines
1324--1400 of `Papers/1804.04964/paper_normal.tex`). The companion
`TNLean.PEPS.RegionBlock.UnionInjectivityOverlap` lands the two host three-block
geometries (`overlapLeftGeometry`, `overlapRightGeometry`) and the first inverse
application `overlap_firstStrip`. This file supplies the remaining sub-step -- the
`P₁`--`P₀` crossing multiplicity collapse -- and assembles the full overlapping union
theorem `regionBlockedTensorInjective_union_overlap`.

With the four parts `P₀ = R₁ \ R₂`, `P₁ = R₁ ∩ R₂`, `P₂ = R₂ \ R₁`, the left
geometry's complement coupling `threeBlockComplCoeff` (over `overlapLeftGeometry`,
constrained by the host `R₁ ∪ R₂` label and the `R₁` boundary label) and the right
geometry's complement coupling (over `overlapRightGeometry`, constrained by the host
`R₂` label and the `P₁` boundary label) are both sums of the same `P₂` vertex product
over global virtual configurations, differing only in the boundary constraints. The
bridge re-partitioning the first by the second is the multiplicity collapse over the
`P₁`--`P₀` edges, which are free in the left coupling (both endpoints in `R₁`, neither
a host nor an `R₁` boundary edge) but pinned by the `R₂` host constraint of the right
geometry.

The key set-theoretic fact making the landed collapse machinery reusable is that, in
the right geometry, `P₀ = R₁ \ R₂` lies entirely inside the red block `R₂ᶜ`, so every
`P₁`--`P₀` edge is a blue/red crossing edge of `overlapRightGeometry`. The landed
`blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq` over the right geometry then
collapses the right coupling onto the `P₂` blocked-region weights; combined with the
right geometry's blue-side factorization, this rebuilds the `R₂` blocked weights, and
the left inverse for `R₂` forces the reconstructed host residual coefficients to
vanish.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `injective_union`, lines 1324--1400 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### `P₀ ⊆ R₂ᶜ`: the right geometry red block contains the difference block

In the right geometry `overlapRightGeometry R₁ R₂` the red block is `R₂ᶜ`, the blue
block is the overlap `R₁ ∩ R₂`, and the complement block is `R₂ \ R₁`. The difference
block `P₀ = R₁ \ R₂` lies inside `R₂ᶜ = red`, so every internal `P₁`--`P₀` edge has one
endpoint in the blue block and one in the red block: it is a blue/red crossing edge of
the right geometry. -/

omit [LinearOrder V] [DecidableRel G.Adj] in
/-- The difference block `R₁ \ R₂` lies inside the right geometry red block `R₂ᶜ`. -/
theorem overlapRightGeometry_sdiff_subset_red (R₁ R₂ : Finset V) :
    R₁ \ R₂ ⊆ (overlapRightGeometry (V := V) R₁ R₂).red := by
  rw [overlapRightGeometry_red]
  intro v hv
  rw [Finset.mem_sdiff] at hv ⊢
  exact ⟨Finset.mem_univ _, hv.2⟩

/-! ### The right geometry blue-side host-weight collapse

The right geometry `g := overlapRightGeometry R₁ R₂` has host `univ \ g.red = R₂`, blue
block `R₁ ∩ R₂`, and complement block `R₂ \ R₁`. The blue-side factorization
`regionInteriorBondProd_smul_geometryBlueWeight_eq` over `g` expresses the positive
overlap-interior-bond multiple of the host weight, read as a function of the overlap leg,
as the overlap-coupling combination of the overlap blocked weights.

The closure feeds this factorization a coefficient row over host boundary configurations
whose right-coupling combination vanishes for every difference leg and overlap boundary
configuration; the factorization then produces a vanishing host-weight combination, read
through the fused overlap/difference leg. -/

open scoped Classical in
/-- **The right blue-side host-weight collapse.** For a coefficient row over the right
geometry's host boundary configurations whose right-coupling combination
`∑ bdry₂, row bdry₂ • threeBlockComplCoeff(bdry₂, σcompl, bβ)` vanishes for every
difference leg `σcompl` and overlap boundary configuration `bβ`, the row's combination of
the host weights, scaled by the positive overlap interior bond product and read through
any fused overlap/difference leg, vanishes.

The right geometry's blue-side factorization rewrites the scaled host weight as the
overlap-coupling combination of the overlap blocked weights; distributing the row
coefficients through and applying the vanishing coupling combination to each overlap
boundary configuration leaves zero.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlapRight_bondProd_smul_hostWeight_combination_eq_zero
    {R₁ R₂ : Finset V}
    (row : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) → ℂ)
    (hrow : ∀ (σcompl : RegionPhysicalConfig (V := V) (d := d)
          (overlapRightGeometry (V := V) R₁ R₂).complement)
        (bβ : RegionBoundaryConfig (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue),
        ∑ bdry₂ : RegionBoundaryConfig (G := G) A
            (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
          row bdry₂ •
            (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ = 0)
    (σblue : RegionPhysicalConfig (V := V) (d := d)
        (overlapRightGeometry (V := V) R₁ R₂).blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d)
        (overlapRightGeometry (V := V) R₁ R₂).complement) :
    (regionInteriorBondProd (G := G) A
          (overlapRightGeometry (V := V) R₁ R₂).blue : ℂ) •
        ∑ bdry₂ : RegionBoundaryConfig (G := G) A
            (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
          row bdry₂ • regionBlockedWeight (G := G) A
            (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) bdry₂
            ((overlapRightGeometry (V := V) R₁ R₂).complPhysical σblue σcompl) = 0 := by
  classical
  -- Scale each host weight by the overlap interior bond product and apply the blue-side
  -- factorization read as a function of the overlap leg.
  rw [Finset.smul_sum]
  rw [Finset.sum_congr rfl (g := fun bdry₂ =>
        row bdry₂ • ∑ bβ : RegionBoundaryConfig (G := G) A
            (overlapRightGeometry (V := V) R₁ R₂).blue,
          (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ •
            regionBlockedWeight (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue bβ σblue)
      (fun bdry₂ _ => by
        rw [smul_comm]
        congr 1
        have := congrFun (regionInteriorBondProd_smul_geometryBlueWeight_eq
          (overlapRightGeometry (V := V) R₁ R₂) (A := A) bdry₂ σcompl) σblue
        rw [Pi.smul_apply, Finset.sum_apply] at this
        rw [this]
        exact Finset.sum_congr rfl (fun bβ _ => by rw [Pi.smul_apply]))]
  -- Swap the `bdry₂` and `bβ` summation order; the inner `bdry₂`-combination is the
  -- vanishing right-coupling combination scaled into each overlap weight.
  rw [Finset.sum_congr rfl (g := fun bdry₂ =>
        ∑ bβ : RegionBoundaryConfig (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue,
          (row bdry₂ •
              (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ) •
            regionBlockedWeight (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue bβ σblue)
      (fun bdry₂ _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun bβ _ => by rw [smul_assoc])),
    Finset.sum_comm]
  refine Finset.sum_eq_zero (fun bβ _ => ?_)
  rw [← Finset.sum_smul]
  rw [show (∑ bdry₂ : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
        row bdry₂ •
          (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ) = 0
      from hrow σcompl bβ, zero_smul]

/-! ### The `P₁`--`P₀` crossing edges

The internal `P₁`--`P₀` edges -- edges with one endpoint in the overlap `R₁ ∩ R₂` and
one in the difference `R₁ \ R₂`, hence both endpoints in `R₁` -- are the edges that are
free in the left geometry's coupling (both endpoints in the left blue block `R₁`, so the
edge is neither a host `R₁ ∪ R₂` boundary edge nor an `R₁` boundary edge) but pinned by
the right geometry's host `R₂` boundary (`P₁ ⊆ R₂`, `P₀ ∩ R₂ = ∅`). They are exactly the
`R₂` boundary edges with both endpoints in `R₁`.

In the right geometry these are blue/red crossing edges: the overlap `P₁` is the blue
block, and `P₀ = R₁ \ R₂` lies inside the red block `R₂ᶜ`
(`overlapRightGeometry_sdiff_subset_red`). -/

/-- An edge is a `P₁`--`P₀` crossing edge when exactly one endpoint lies in the overlap
`R₁ ∩ R₂` and the other lies in the difference `R₁ \ R₂`. Both endpoints lie in `R₁`. -/
def IsOverlapCrossingEdge (R₁ R₂ : Finset V) (eg : Edge G) : Prop :=
  (eg.1.1 ∈ R₁ ∩ R₂ ∧ eg.1.2 ∈ R₁ \ R₂) ∨ (eg.1.1 ∈ R₁ \ R₂ ∧ eg.1.2 ∈ R₁ ∩ R₂)

instance (R₁ R₂ : Finset V) (eg : Edge G) :
    Decidable (IsOverlapCrossingEdge (G := G) R₁ R₂ eg) := by
  unfold IsOverlapCrossingEdge; infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- Both endpoints of a `P₁`--`P₀` crossing edge lie in `R₁`. -/
theorem isOverlapCrossingEdge_both_mem_R₁ {R₁ R₂ : Finset V} {eg : Edge G}
    (h : IsOverlapCrossingEdge (G := G) R₁ R₂ eg) : eg.1.1 ∈ R₁ ∧ eg.1.2 ∈ R₁ := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_sdiff.mp h2).1⟩
  · exact ⟨(Finset.mem_sdiff.mp h1).1, (Finset.mem_inter.mp h2).1⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A `P₁`--`P₀` crossing edge is a boundary edge of `R₂`: its overlap endpoint lies in
`R₂` while its difference endpoint lies outside `R₂`. -/
theorem isRegionBoundaryEdge_R₂_of_overlapCrossing {R₁ R₂ : Finset V} {eg : Edge G}
    (h : IsOverlapCrossingEdge (G := G) R₁ R₂ eg) :
    IsRegionBoundaryEdge (G := G) R₂ eg := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨(Finset.mem_inter.mp h1).2, (Finset.mem_sdiff.mp h2).2⟩
  · exact Or.inr ⟨(Finset.mem_sdiff.mp h1).2, (Finset.mem_inter.mp h2).2⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A `P₁`--`P₀` crossing edge is not a boundary edge of `R₁`: both endpoints lie in
`R₁`. -/
theorem not_isRegionBoundaryEdge_R₁_of_overlapCrossing {R₁ R₂ : Finset V} {eg : Edge G}
    (h : IsOverlapCrossingEdge (G := G) R₁ R₂ eg) :
    ¬ IsRegionBoundaryEdge (G := G) R₁ eg := by
  obtain ⟨h1, h2⟩ := isOverlapCrossingEdge_both_mem_R₁ (G := G) h
  rintro (⟨_, h2'⟩ | ⟨h1', _⟩)
  · exact h2' h2
  · exact h1' h1

omit [Fintype V] [DecidableRel G.Adj] in
/-- A `P₁`--`P₀` crossing edge is not a boundary edge of the union `R₁ ∪ R₂`: both
endpoints lie in `R₁ ⊆ R₁ ∪ R₂`. -/
theorem not_isRegionBoundaryEdge_union_of_overlapCrossing {R₁ R₂ : Finset V} {eg : Edge G}
    (h : IsOverlapCrossingEdge (G := G) R₁ R₂ eg) :
    ¬ IsRegionBoundaryEdge (G := G) (R₁ ∪ R₂) eg := by
  obtain ⟨h1, h2⟩ := isOverlapCrossingEdge_both_mem_R₁ (G := G) h
  rintro (⟨_, h2'⟩ | ⟨h1', _⟩)
  · exact h2' (Finset.mem_union_left _ h2)
  · exact h1' (Finset.mem_union_left _ h1)

/-- A `P₁`--`P₀` crossing edge is a blue/red crossing edge of the right geometry: its
overlap endpoint lies in the blue block `R₁ ∩ R₂`, and its difference endpoint lies in
the red block `R₂ᶜ`. This identifies the crossing-edge family with the blue/red crossings
of `overlapRightGeometry`, so the landed right-geometry collapse acts over them. -/
theorem isBlueRedCrossingEdge_right_of_overlapCrossing {R₁ R₂ : Finset V} {eg : Edge G}
    (h : IsOverlapCrossingEdge (G := G) R₁ R₂ eg) :
    (overlapRightGeometry (V := V) R₁ R₂).IsBlueRedCrossingEdge A eg := by
  refine ⟨?_, ?_⟩
  · -- A boundary edge of the red block `R₂ᶜ`: the overlap endpoint is in `R₂`, hence not
    -- in `R₂ᶜ`, and the difference endpoint is outside `R₂`, hence in `R₂ᶜ`.
    rw [overlapRightGeometry_red]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [Finset.mem_sdiff]
        push Not
        exact fun _ => (Finset.mem_inter.mp h1).2
      · rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp h2).2⟩
    · refine Or.inl ⟨?_, ?_⟩
      · rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp h1).2⟩
      · rw [Finset.mem_sdiff]
        push Not
        exact fun _ => (Finset.mem_inter.mp h2).2
  · -- A boundary edge of the blue block `R₁ ∩ R₂`.
    rw [overlapRightGeometry_blue]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun hc => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp hc).2⟩
    · exact Or.inr ⟨fun hc => (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp hc).2, h2⟩

end PEPS
end TNLean
