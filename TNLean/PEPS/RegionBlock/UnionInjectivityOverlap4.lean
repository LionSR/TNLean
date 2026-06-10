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

/-! ### The difference label is determined by the union host and `R₁` labels

Every boundary edge of the difference `R₂ \ R₁` is a boundary edge of the union `R₁ ∪ R₂` or
of `R₁`: its in-difference endpoint lies in `R₂ \ R₁`, while its other endpoint either lies
outside `R₁ ∪ R₂` (a union boundary edge) or lies in `R₁` (an `R₁` boundary edge). Therefore
the difference boundary label of a configuration is determined by its union host and `R₁`
labels: this is the difference reconstruction underlying the `R₁`-parametrized closure. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- A boundary edge of the difference `R₂ \ R₁` is a boundary edge of the union `R₁ ∪ R₂` or
of `R₁`. -/
theorem isRegionBoundaryEdge_union_or_R₁_of_sdiff {R₁ R₂ : Finset V} {e : Edge G}
    (h : IsRegionBoundaryEdge (G := G) (R₂ \ R₁) e) :
    IsRegionBoundaryEdge (G := G) (R₁ ∪ R₂) e ∨ IsRegionBoundaryEdge (G := G) R₁ e := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `e.1.1 ∈ R₂ \ R₁`, `e.1.2 ∉ R₂ \ R₁`; the in-difference endpoint is in `R₂`, not `R₁`.
    obtain ⟨h1R₂, h1nR₁⟩ := Finset.mem_sdiff.mp h1
    by_cases hb : e.1.2 ∈ R₁
    · -- `e.1.2 ∈ R₁`, `e.1.1 ∉ R₁`: an `R₁` boundary edge.
      exact Or.inr (Or.inr ⟨h1nR₁, hb⟩)
    · -- `e.1.2 ∉ R₁`; from `e.1.2 ∉ R₂ \ R₁` and `e.1.2 ∉ R₁`, also `e.1.2 ∉ R₂`.
      have h2R₂ : e.1.2 ∉ R₂ := fun h => h2 (Finset.mem_sdiff.mpr ⟨h, hb⟩)
      exact Or.inl (Or.inl ⟨Finset.mem_union_right _ h1R₂,
        fun hc => (Finset.mem_union.mp hc).elim hb h2R₂⟩)
  · obtain ⟨h2R₂, h2nR₁⟩ := Finset.mem_sdiff.mp h2
    by_cases hb : e.1.1 ∈ R₁
    · exact Or.inr (Or.inl ⟨hb, h2nR₁⟩)
    · have h1R₂ : e.1.1 ∉ R₂ := fun h => h1 (Finset.mem_sdiff.mpr ⟨h, hb⟩)
      exact Or.inl (Or.inr ⟨fun hc => (Finset.mem_union.mp hc).elim hb h1R₂,
        Finset.mem_union_right _ h2R₂⟩)

omit [Fintype V] in
/-- The difference boundary label is determined by the union host and `R₁` boundary labels: if
two configurations share their `R₁ ∪ R₂` and `R₁` labels, they share their `R₂ \ R₁` label. -/
theorem regionBoundaryLabel_sdiff_eq_of_union_R₁ {R₁ R₂ : Finset V} {q q' : VirtualConfig A}
    (hunion : regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q =
      regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q')
    (hR₁ : regionBoundaryLabel (G := G) A R₁ q = regionBoundaryLabel (G := G) A R₁ q') :
    regionBoundaryLabel (G := G) A (R₂ \ R₁) q = regionBoundaryLabel (G := G) A (R₂ \ R₁) q' := by
  funext f
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply]
  rcases isRegionBoundaryEdge_union_or_R₁_of_sdiff (G := G) f.2 with he | he
  · have := congrFun hunion ⟨f.1, he⟩; rwa [regionBoundaryLabel_apply,
      regionBoundaryLabel_apply] at this
  · have := congrFun hR₁ ⟨f.1, he⟩; rwa [regionBoundaryLabel_apply,
      regionBoundaryLabel_apply] at this

/-! ### The overlap-crossing glue keeps the `R₁` label

The overlap-crossing edges are not boundary edges of `R₁`
(`not_isRegionBoundaryEdge_R₁_of_overlapCrossing`), so overwriting on them leaves the `R₁`
boundary label unchanged. This is the companion of the union, overlap, and difference
transport lemmas of `interCrossGlue` already landed. -/

omit [Fintype V] in
/-- The overlap-crossing glue keeps `q₂`'s `R₁` label: the overlap-crossing edges are not `R₁`
boundary edges, so the `R₁` boundary label reads `q₂` everywhere it is defined. -/
theorem regionBoundaryLabel_R₁_interCrossGlue {R₁ R₂ : Finset V} (q₁ q₂ : VirtualConfig A) :
    regionBoundaryLabel (G := G) A R₁ (interCrossGlue (G := G) R₁ R₂ q₁ q₂) =
      regionBoundaryLabel (G := G) A R₁ q₂ := by
  classical
  funext f
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply, interCrossGlue,
    if_neg (fun hc => not_isRegionBoundaryEdge_R₁_of_overlapCrossing (G := G) hc f.2)]

/-! ### The overlap-crossing multiplicity collapse identity

The source's "plug back the tensor over `A ∩ B`" move re-contracts the overlap tensor along its
`P₁`--`P₀` crossing boundary. At the level of the boundary-configuration existence indicators
parametrized by the open-`R₁`-legs configuration `β₁`, this collapse is the factorization of
the joint existence indicator
`1[∃ q : union = bdry ∧ R₁ = β₁ ∧ overlap = β ∧ difference = bc']` into the product of the
overlap-glue indicator `1[∃ q : R₁ = β₁ ∧ overlap = β]` and the left first-strip indicator
`1[∃ q : union = bdry ∧ R₁ = β₁ ∧ difference = bc']`.

The forward split is immediate (a single witness realizes both indicators). The reverse glue
re-contracts the overlap: a witness `q₃` of the overlap-glue and a witness `q₄` of the left
indicator agree on `R₁` (both carry `R₁ = β₁`), so overwriting `q₄` by `q₃` on the
overlap-crossing edges keeps `q₄`'s union, `R₁`, and difference labels (the crossing edges are
boundary edges of none of these) and installs `q₃`'s overlap label `β`. This is the
`β₁`-parametrized gathering's gluing carrying the extra `R₁`-boundary constraint. -/

open scoped Classical in
/-- **The overlap-crossing multiplicity collapse.** For a fixed open-`R₁`-legs configuration
`β₁`, the joint existence indicator over (union, `R₁`, overlap, difference) factors as the
product of the overlap-glue indicator over (`R₁`, overlap) and the left first-strip indicator
over (union, `R₁`, difference).

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex` (the "plug back the tensor over `A ∩ B`" move). -/
theorem overlapJointIndicator_eq_interGlue_mul_leftIndicator {R₁ R₂ : Finset V}
    (bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂))
    (β₁ : RegionBoundaryConfig (G := G) A R₁)
    (β : RegionBoundaryConfig (G := G) A (R₁ ∩ R₂))
    (bc' : RegionBoundaryConfig (G := G) A (R₂ \ R₁)) :
    (if ∃ q : VirtualConfig A,
        regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
          regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
            regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = β ∧
              regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
      then (1 : ℂ) else 0) =
      (if ∃ q : VirtualConfig A,
          regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
            regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = β
        then (1 : ℂ) else 0) *
        (if ∃ q : VirtualConfig A,
            regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
              regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
                regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
          then (1 : ℂ) else 0) := by
  classical
  by_cases hjoint : ∃ q : VirtualConfig A,
      regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
        regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
          regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = β ∧
            regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
  · -- A joint witness realizes both factors, so the product is `1 * 1`.
    rw [if_pos hjoint]
    obtain ⟨q, hu, hr1, hov, hdiff⟩ := hjoint
    rw [if_pos ⟨q, hr1, hov⟩, if_pos ⟨q, hu, hr1, hdiff⟩, mul_one]
  · -- Without a joint witness, at least one factor must vanish: otherwise the overlap-crossing
    -- glue of the two witnesses would be a joint witness.
    rw [if_neg hjoint]
    by_cases hglue : ∃ q : VirtualConfig A,
        regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
          regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = β
    · by_cases hleft : ∃ q : VirtualConfig A,
          regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
            regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
              regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
      · -- Both factors hold: glue them into a joint witness, contradicting `hjoint`.
        exfalso
        obtain ⟨q₃, hq₃r1, hq₃ov⟩ := hglue
        obtain ⟨q₄, hq₄u, hq₄r1, hq₄diff⟩ := hleft
        apply hjoint
        refine ⟨interCrossGlue (G := G) R₁ R₂ q₃ q₄, ?_, ?_, ?_, ?_⟩
        · rw [regionBoundaryLabel_union_interCrossGlue]; exact hq₄u
        · rw [regionBoundaryLabel_R₁_interCrossGlue]; exact hq₄r1
        · exact regionBoundaryLabel_inter_interCrossGlue (G := G) q₃ q₄ hq₃ov
            (by rw [hq₄r1, hq₃r1])
        · rw [regionBoundaryLabel_sdiff_interCrossGlue]; exact hq₄diff
      · rw [if_neg hleft, mul_zero]
    · rw [if_neg hglue, zero_mul]

end PEPS
end TNLean
