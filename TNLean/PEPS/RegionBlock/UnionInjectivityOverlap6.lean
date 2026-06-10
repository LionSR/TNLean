import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap5

/-!
# The overlapping union lemma: the overlap re-insertion and the closure

This file closes the source's overlapping union-of-injective-regions lemma of the normal PEPS
Fundamental Theorem (arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`). The companions `UnionInjectivityOverlap`, `2`, `3`, `4`,
and `5` land the two host three-block geometries, the first inverse application
`overlap_firstStrip`, the right-geometry blue-side rebuild, the `P₀`-outer bridge, the host and
difference reconstructions, and the overlap-crossing multiplicity collapse.

## The remaining obstruction and the fix

The landed chain inverts `R₁` (the left strip) and then re-inserts the overlap `R₁ ∩ R₂` and
inverts `R₂` (the right rebuild). With the four parts `P₀ = R₁ \ R₂`, `P₁ = R₁ ∩ R₂`,
`P₂ = R₂ \ R₁`, the rebuild reads the `R₂` blocked weights through the fused overlap/difference
leg, so the right-rebuild row is indexed by `R₂` boundary configurations. Inverting `R₂` forces
that row to vanish. As recorded in obligation 1 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, an `R₂`-only row cannot separate the
`P₀`-outer host indices: the union host boundary edges partition into `R₂` boundary edges and
`P₀`-outer edges (the union boundary edges from `R₁ \ R₂` to `(R₁ ∪ R₂)ᶜ`), and a row over `R₂`
alone leaves the `P₀`-outer freedom undetermined.

The source resolves this by leaving the `R₁ \ R₂` open legs uncontracted through the
re-insertion: after inverting `R₂`, the `P₀`-side legs are the open legs of the final tensor.
The present file carries those legs as the `P₀`-outer label. The key observations:

* The `P₀`-outer edges are disjoint from the `R₂`, overlap, and difference boundary edges (both
  endpoints of a `P₀`-outer edge lie outside `R₂`), so the `P₀`-outer label is an independent
  parameter that the right rebuild does not touch.
* A `P₀`-outer edge is a boundary edge of `R₁`, so the `R₁` boundary label determines the
  `P₀`-outer label.
* The union host boundary label is determined by the pair (`R₂` boundary label, `P₀`-outer
  label), because the union boundary edges partition into the two families.

Fixing the `P₀`-outer label to a reference `δ` and restricting the coefficient family `c` to the
`P₀`-fiber `{bdry : bdry|P₀ = δ}` gives a row whose right coupling, read through the
overlap-crossing collapse, is a sum of the left first strips restricted to the same fiber. Each
restricted strip is either zero (when the `R₁` boundary label has the wrong `P₀`-outer part) or
the full first strip (which already vanishes), so the right coupling vanishes. The right rebuild
then produces a vanishing combination of the `R₂` blocked weights of the fiber-restricted bridge
row; injectivity of `R₂` forces that row to vanish. Finally, at any host label, fixing `δ` to its
`P₀`-outer part and `b₂` to its `R₂` part selects a single host term by the partition
determinacy, forcing `c = 0` at every realizable host label. Host-boundary surjectivity covers
every label.

The result is `regionBlockedTensorInjective_union_overlap`: for `R₁`, `R₂` both blocked-tensor
injective and all bond dimensions positive, the union `R₁ ∪ R₂` is blocked-tensor injective.

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

/-! ### The `P₀`-outer label and its determinacy

The `P₀`-outer edges (the union `R₁ ∪ R₂` boundary edges that are not `R₂` boundary edges, running
from `R₁ \ R₂` to `(R₁ ∪ R₂)ᶜ`) are the open legs of the final tensor in the source proof. The
`P₀`-outer label of a configuration reads its virtual indices on these edges. -/

/-- The type of `P₀`-outer boundary configurations: virtual indices on the `P₀`-outer edges (the
union `R₁ ∪ R₂` boundary edges that are not `R₂` boundary edges). -/
abbrev P0OuterConfig (A : Tensor G d) (R₁ R₂ : Finset V) : Type _ :=
  (e : {e : Edge G // IsP0OuterEdge (G := G) R₁ R₂ e}) → Fin (A.bondDim e.1)

/-- The `P₀`-outer label read off a global virtual configuration: its virtual indices on the
`P₀`-outer edges. -/
def p0OuterLabel (A : Tensor G d) (R₁ R₂ : Finset V) (ζ : VirtualConfig A) :
    P0OuterConfig A R₁ R₂ := fun f => ζ f.1

omit [Fintype V] in
@[simp] theorem p0OuterLabel_apply (R₁ R₂ : Finset V) (ζ : VirtualConfig A)
    (f : {e : Edge G // IsP0OuterEdge (G := G) R₁ R₂ e}) :
    p0OuterLabel A R₁ R₂ ζ f = ζ f.1 := rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- A `P₀`-outer edge is a boundary edge of `R₁`: one endpoint lies in `R₁ \ R₂ ⊆ R₁`, the other
lies outside `R₁ ∪ R₂`, hence outside `R₁`. -/
theorem isRegionBoundaryEdge_R₁_of_p0Outer {R₁ R₂ : Finset V} {e : Edge G}
    (h : IsP0OuterEdge (G := G) R₁ R₂ e) : IsRegionBoundaryEdge (G := G) R₁ e := by
  obtain ⟨h1, h2⟩ := isP0OuterEdge_both_not_mem_R₂ (G := G) h
  obtain ⟨hunion, _⟩ := h
  rcases hunion with ⟨h1u, h2nu⟩ | ⟨h1nu, h2u⟩
  · refine Or.inl ⟨(Finset.mem_union.mp h1u).resolve_right h1, ?_⟩
    exact fun hc => h2nu (Finset.mem_union_left _ hc)
  · refine Or.inr ⟨fun hc => h1nu (Finset.mem_union_left _ hc), ?_⟩
    exact (Finset.mem_union.mp h2u).resolve_right h2

omit [Fintype V] in
/-- The `R₁` boundary label determines the `P₀`-outer label: if two configurations share their
`R₁` label, they share their `P₀`-outer label. -/
theorem p0OuterLabel_eq_of_R₁ {R₁ R₂ : Finset V} {q q' : VirtualConfig A}
    (h : regionBoundaryLabel (G := G) A R₁ q = regionBoundaryLabel (G := G) A R₁ q') :
    p0OuterLabel A R₁ R₂ q = p0OuterLabel A R₁ R₂ q' := by
  funext f
  have := congrFun h ⟨f.1, isRegionBoundaryEdge_R₁_of_p0Outer (G := G) f.2⟩
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply] at this
  rw [p0OuterLabel, p0OuterLabel, this]

omit [Fintype V] in
/-- The union host boundary label determines the `P₀`-outer label: the `P₀`-outer edges are union
boundary edges, so a configuration's `P₀`-outer label is read off its union host label. -/
theorem p0OuterLabel_eq_of_union {R₁ R₂ : Finset V} {q q' : VirtualConfig A}
    (h : regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q =
      regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q') :
    p0OuterLabel A R₁ R₂ q = p0OuterLabel A R₁ R₂ q' := by
  funext f
  have := congrFun h ⟨f.1, f.2.1⟩
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply] at this
  rw [p0OuterLabel, p0OuterLabel, this]

omit [Fintype V] in
/-- The union host boundary label is determined by the pair (`R₂` boundary label, `P₀`-outer
label): the union boundary edges partition into `R₂` boundary edges and `P₀`-outer edges, so if
two configurations share both their `R₂` and `P₀`-outer labels, they share their `R₁ ∪ R₂`
label. -/
theorem regionBoundaryLabel_union_eq_of_R₂_p0Outer {R₁ R₂ : Finset V} {q q' : VirtualConfig A}
    (hR₂ : regionBoundaryLabel (G := G) A R₂ q = regionBoundaryLabel (G := G) A R₂ q')
    (hδ : p0OuterLabel A R₁ R₂ q = p0OuterLabel A R₁ R₂ q') :
    regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q =
      regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q' := by
  funext f
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply]
  by_cases hR₂edge : IsRegionBoundaryEdge (G := G) R₂ f.1
  · have := congrFun hR₂ ⟨f.1, hR₂edge⟩
    rwa [regionBoundaryLabel_apply, regionBoundaryLabel_apply] at this
  · have hp0 : IsP0OuterEdge (G := G) R₁ R₂ f.1 := ⟨f.2, hR₂edge⟩
    have := congrFun hδ ⟨f.1, hp0⟩
    rwa [p0OuterLabel, p0OuterLabel] at this

/-! ### The `P₀`-restriction of a host boundary configuration and the fiber coefficient

The `P₀`-restriction of a union host boundary configuration reads its values on the `P₀`-outer
sub-edges. The fiber coefficient zeroes a coefficient family `c` off the `P₀`-fiber of a fixed
reference `δ`. -/

omit [Fintype V] in
/-- The `P₀`-restriction of a union host boundary configuration: read off its `P₀`-outer
sub-edges. A configuration's `P₀`-outer label is the `P₀`-restriction of its union host label. -/
theorem p0OuterLabel_apply_subtype {R₁ R₂ : Finset V} (q : VirtualConfig A)
    (f : {e : Edge G // IsP0OuterEdge (G := G) R₁ R₂ e}) :
    p0OuterLabel A R₁ R₂ q f =
      regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q ⟨f.1, f.2.1⟩ := rfl

/-- The `P₀`-restriction of a union host boundary configuration: its values on the `P₀`-outer
sub-edges. -/
def unionToP0Outer {R₁ R₂ : Finset V}
    (bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂)) : P0OuterConfig A R₁ R₂ :=
  fun f => bdry ⟨f.1, f.2.1⟩

omit [Fintype V] in
/-- The `P₀`-outer label of a configuration is the `P₀`-restriction of its union host label. -/
theorem unionToP0Outer_regionBoundaryLabel {R₁ R₂ : Finset V} (q : VirtualConfig A) :
    unionToP0Outer (A := A) (regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q) =
      p0OuterLabel A R₁ R₂ q := rfl

open scoped Classical in
/-- The coefficient family `c` restricted to the `P₀`-fiber of a reference `δ`: it equals `c` on
the host configurations whose `P₀`-restriction is `δ` and vanishes elsewhere. -/
noncomputable def cFiber {R₁ R₂ : Finset V}
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ) (δ : P0OuterConfig A R₁ R₂) :
    RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ :=
  fun bdry => if unionToP0Outer (A := A) bdry = δ then c bdry else 0

/-! ### The `P₀`-fiber-restricted first strip vanishes

The left first strip read through the overlap-crossing collapse vanishes for every `R₁` boundary
label `β₁` (`overlapLeft_firstStrip_weightCombination_eq_zero`). Restricting the coefficient
family to the `P₀`-fiber of a reference `δ` preserves this vanishing. There are two cases. If every
configuration realizing the `R₁` label `β₁` has `P₀`-outer label `δ`, the fiber restriction is
redundant on the strip's existence indicator (which requires `R₁ = β₁`), so the restricted strip is
the full strip, which vanishes. Otherwise some configuration realizing `β₁` has `P₀`-outer label
other than `δ`, hence every configuration realizing `β₁` does (the `R₁` label determines the
`P₀`-outer label), so every fiber coefficient surviving the strip's indicator is zero. -/

open scoped Classical in
/-- **The `P₀`-fiber-restricted first strip vanishes.** For a coefficient family `c` annihilating
the host blocked weights, `R₁` blocked-tensor injective, a reference `P₀`-outer label `δ`, and an
`R₁` boundary label `β₁`, the `δ`-fiber-restricted left-indicator combination of the `R₂ \ R₁`
blocked weights is zero.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlapLeft_firstStrip_fiber_weightCombination_eq_zero {R₁ R₂ : Finset V}
    (hR₁ : RegionBlockedTensorInjective (G := G) A R₁)
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red),
        (fun b => c (regionBoundaryConfigCongr (A := A)
            (overlapLeftGeometry_univ_sdiff_red R₁ R₂) b)) bdry •
          regionBlockedWeight (G := G) A
            (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) bdry = 0)
    (δ : P0OuterConfig A R₁ R₂)
    (β₁ : RegionBoundaryConfig (G := G) A R₁)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) (R₂ \ R₁)) :
    ∑ bc' : RegionBoundaryConfig (G := G) A (R₂ \ R₁),
        (∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
            cFiber (A := A) c δ bdry *
              (if ∃ q : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
                    regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
                      regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
                then (1 : ℂ) else 0)) •
          regionBlockedWeight (G := G) A (R₂ \ R₁) bc' σcompl = 0 := by
  classical
  by_cases hβδ : ∀ q : VirtualConfig A, regionBoundaryLabel (G := G) A R₁ q = β₁ →
      p0OuterLabel A R₁ R₂ q = δ
  · -- The fiber restriction is redundant: `cFiber c δ` may be replaced by `c` inside the strip.
    have hrepl : ∀ bc' : RegionBoundaryConfig (G := G) A (R₂ \ R₁),
        (∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
            cFiber (A := A) c δ bdry *
              (if ∃ q : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
                    regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
                      regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
                then (1 : ℂ) else 0)) =
          ∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
            c bdry *
              (if ∃ q : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
                    regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
                      regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
                then (1 : ℂ) else 0) := by
      intro bc'
      refine Finset.sum_congr rfl (fun bdry _ => ?_)
      by_cases hind : ∃ q : VirtualConfig A,
          regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
            regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
              regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
      · obtain ⟨q, hu, hr, _⟩ := hind
        have hδbdry : unionToP0Outer (A := A) bdry = δ := by
          rw [← hu, unionToP0Outer_regionBoundaryLabel]; exact hβδ q hr
        rw [cFiber, if_pos hδbdry]
      · rw [if_neg hind, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun bc' _ => by rw [hrepl bc'])]
    exact overlapLeft_firstStrip_weightCombination_eq_zero (G := G) (A := A) hR₁ c hc β₁ σcompl
  · -- Some configuration realizes `β₁` with `P₀`-outer label other than `δ`; the `R₁` label
    -- determines the `P₀`-outer label, so every surviving fiber coefficient is zero.
    push Not at hβδ
    obtain ⟨q₀, hq₀r, hq₀δ⟩ := hβδ
    refine Finset.sum_eq_zero (fun bc' _ => ?_)
    rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
          cFiber (A := A) c δ bdry *
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
                  regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
                    regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
              then (1 : ℂ) else 0)) = 0 from ?_, zero_smul]
    refine Finset.sum_eq_zero (fun bdry _ => ?_)
    by_cases hind : ∃ q : VirtualConfig A,
        regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
          regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
            regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
    · obtain ⟨q, hu, hr, _⟩ := hind
      have hpq : p0OuterLabel A R₁ R₂ q = p0OuterLabel A R₁ R₂ q₀ :=
        p0OuterLabel_eq_of_R₁ (G := G) (hr.trans hq₀r.symm)
      have hδbdry : unionToP0Outer (A := A) bdry ≠ δ := by
        rw [← hu, unionToP0Outer_regionBoundaryLabel, hpq]; exact hq₀δ
      rw [cFiber, if_neg hδbdry, zero_mul]
    · rw [if_neg hind, mul_zero]

end PEPS
end TNLean
