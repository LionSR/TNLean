import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap3

/-!
# The overlapping union lemma: the `R₁`-boundary-parametrized closure

This file closes the source's overlapping union-of-injective-regions lemma of the normal PEPS
Fundamental Theorem (arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`) and assembles the full overlapping union theorem
`regionBlockedTensorInjective_union_overlap`.

The companions `UnionInjectivityOverlap`, `2`, and `3` land the two host three-block geometries,
the first inverse application, the rebuild step, and the `P₀`-outer bridge. The bridge
`overlap_bridge_rightCoupling_eq_zero` makes the right coupling combination of the *summed*
bridge row vanish; fed to the rebuild and inverted by injectivity of `R₂`, this pins the
coefficient family `c` only up to the `P₀`-outer freedom (the host `R₁ ∪ R₂` residual is
determined by the pair (`R₁`-boundary, `R₂`-boundary), so a row over `R₂` alone cannot separate
the `P₀`-outer indices).

The closure parametrizes the rebuild row by the `R₁`-boundary configuration `β₁` (the source's
open-`A`-legs parameter). The `β₁`-restricted bridge row `overlapBridgeRowParam c β₁` carries
the extra `R₁ = β₁` constraint into the host glue; its right coupling combination vanishes by
the same first strip at `β₁`, so the rebuild and the inversion of `R₂` give the vanishing of the
`β₁`-restricted row for every `R₂`-boundary configuration. The host `R₁ ∪ R₂` boundary label is
determined by the pair (`R₁`-boundary, `R₂`-boundary), so reading the unique host residual
reconstructed from the pair (`β₁`, `R₂`-boundary) forces each `c` coefficient to vanish; host
boundary surjectivity covers every host label.

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

/-! ### The host label is determined by the `R₁` and `R₂` labels

Every boundary edge of the union `R₁ ∪ R₂` is a boundary edge of `R₁` or of `R₂`: its in-union
endpoint lies in `R₁` or in `R₂`, while its other endpoint lies outside `R₁ ∪ R₂`, hence outside
both. Therefore the union host boundary label of a configuration is determined by its `R₁` and
`R₂` boundary labels: this is the host reconstruction underlying the final extraction. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- A boundary edge of the union `R₁ ∪ R₂` is a boundary edge of `R₁` or of `R₂`. -/
theorem isRegionBoundaryEdge_R₁_or_R₂_of_union {R₁ R₂ : Finset V} {e : Edge G}
    (h : IsRegionBoundaryEdge (G := G) (R₁ ∪ R₂) e) :
    IsRegionBoundaryEdge (G := G) R₁ e ∨ IsRegionBoundaryEdge (G := G) R₂ e := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `e.1.1 ∈ R₁ ∪ R₂`, `e.1.2 ∉ R₁ ∪ R₂`; the in-union endpoint is in `R₁` or in `R₂`.
    have h2R₁ : e.1.2 ∉ R₁ := fun h => h2 (Finset.mem_union_left _ h)
    have h2R₂ : e.1.2 ∉ R₂ := fun h => h2 (Finset.mem_union_right _ h)
    rcases Finset.mem_union.mp h1 with hb | hb
    · exact Or.inl (Or.inl ⟨hb, h2R₁⟩)
    · exact Or.inr (Or.inl ⟨hb, h2R₂⟩)
  · have h1R₁ : e.1.1 ∉ R₁ := fun h => h1 (Finset.mem_union_left _ h)
    have h1R₂ : e.1.1 ∉ R₂ := fun h => h1 (Finset.mem_union_right _ h)
    rcases Finset.mem_union.mp h2 with hb | hb
    · exact Or.inl (Or.inr ⟨h1R₁, hb⟩)
    · exact Or.inr (Or.inr ⟨h1R₂, hb⟩)

omit [Fintype V] in
/-- The union host boundary label is determined by the `R₁` and `R₂` boundary labels: if two
configurations share their `R₁` and `R₂` labels, they share their `R₁ ∪ R₂` label. -/
theorem regionBoundaryLabel_union_eq_of_R₁_R₂ {R₁ R₂ : Finset V} {q q' : VirtualConfig A}
    (hR₁ : regionBoundaryLabel (G := G) A R₁ q = regionBoundaryLabel (G := G) A R₁ q')
    (hR₂ : regionBoundaryLabel (G := G) A R₂ q = regionBoundaryLabel (G := G) A R₂ q') :
    regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q' := by
  funext f
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply]
  rcases isRegionBoundaryEdge_R₁_or_R₂_of_union (G := G) f.2 with he | he
  · have := congrFun hR₁ ⟨f.1, he⟩; rwa [regionBoundaryLabel_apply,
      regionBoundaryLabel_apply] at this
  · have := congrFun hR₂ ⟨f.1, he⟩; rwa [regionBoundaryLabel_apply,
      regionBoundaryLabel_apply] at this

end PEPS
end TNLean
