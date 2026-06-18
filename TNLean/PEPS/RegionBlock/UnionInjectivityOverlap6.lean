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

/-! ### The `P₀`-fiber bridge: the right coupling vanishes

The right coupling combination of the `δ`-fiber bridge row, read through the right-geometry
crossing collapse and the bridge coefficient identity, is the overlap-glue-weighted combination of
the `P₀`-fiber-restricted first strips, each vanishing by
`overlapLeft_firstStrip_fiber_weightCombination_eq_zero`. Dividing by the positive right crossing
bond gives the rebuild hypothesis for the fiber bridge row. The bridge coefficient identity
`overlapBridge_coeff_eq` holds for any coefficient family, so the fiber row reuses it directly; the
fiber-restricted strip is what discharges each summand. -/

open scoped Classical in
/-- **The `P₀`-fiber bridge.** For a coefficient family `c` annihilating the host blocked weights,
`R₁` blocked-tensor injective, positive bond dimensions, and a reference `P₀`-outer label `δ`, the
`δ`-fiber bridge row `overlapBridgeRow (cFiber c δ)` (carried to the right host) makes the right
coupling combination vanish for every difference physical leg and overlap boundary configuration.
This is the fiber analogue of `overlap_bridge_rightCoupling_eq_zero`, and the exact hypothesis the
rebuild step `overlapRight_bondProd_smul_hostWeight_combination_eq_zero` consumes.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlapFiber_bridge_rightCoupling_eq_zero {R₁ R₂ : Finset V}
    (hR₁ : RegionBlockedTensorInjective (G := G) A R₁)
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red),
        (fun b => c (regionBoundaryConfigCongr (A := A)
            (overlapLeftGeometry_univ_sdiff_red R₁ R₂) b)) bdry •
          regionBlockedWeight (G := G) A
            (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) bdry = 0)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (δ : P0OuterConfig A R₁ R₂)
    (σcompl : RegionPhysicalConfig (V := V) (d := d)
        (overlapRightGeometry (V := V) R₁ R₂).complement)
    (bβ : RegionBoundaryConfig (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue) :
    ∑ bdry₂ : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
      (fun b => overlapBridgeRow (G := G) (A := A) (cFiber (A := A) c δ)
          (regionBoundaryConfigCongr (A := A)
            (overlapRightGeometry_univ_sdiff_red R₁ R₂) b)) bdry₂ •
        (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ = 0 := by
  classical
  have hHR : Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red = R₂ :=
    overlapRightGeometry_univ_sdiff_red R₁ R₂
  set row : RegionBoundaryConfig (G := G) A
      (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) → ℂ :=
    fun b => overlapBridgeRow (G := G) (A := A) (cFiber (A := A) c δ)
      (regionBoundaryConfigCongr (A := A) hHR b) with hrow
  have hcrosspos : 0 < (overlapRightGeometry (V := V) R₁ R₂).blueRedCrossingBondProd A :=
    (overlapRightGeometry (V := V) R₁ R₂).blueRedCrossingBondProd_pos A hpos
  have hcrossne : ((overlapRightGeometry (V := V) R₁ R₂).blueRedCrossingBondProd A : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcrosspos.ne'
  rw [← smul_right_injective ℂ hcrossne |>.eq_iff (a := _) (b := (0 : _)), smul_zero]
  have hcollapse :=
    (overlapRightGeometry (V := V) R₁ R₂).crossingBond_smul_complCoeff_combination_eq
    (A := A) row bβ σcompl
  rw [hcollapse]
  have hcoeff : ∀ bc' : RegionBoundaryConfig (G := G) A
        (overlapRightGeometry (V := V) R₁ R₂).complement,
      (∑ hostlab : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
          row hostlab •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A
                  (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) q = hostlab ∧
                  regionBoundaryLabel (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue q = bβ ∧
                    regionBoundaryLabel (G := G) A
                      (overlapRightGeometry (V := V) R₁ R₂).complement q = bc'
              then (1 : ℂ) else 0)) =
        ∑ β₁ : RegionBoundaryConfig (G := G) A R₁,
          (if ∃ q₁ : VirtualConfig A,
              regionBoundaryLabel (G := G) A R₁ q₁ = β₁ ∧
                regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q₁ = bβ
            then (1 : ℂ) else 0) *
            ∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
              (cFiber (A := A) c δ) bdry *
                (if ∃ q₂ : VirtualConfig A,
                    regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₂ = bdry ∧
                      regionBoundaryLabel (G := G) A R₁ q₂ = β₁ ∧
                        regionBoundaryLabel (G := G) A (R₂ \ R₁) q₂ = bc'
                  then (1 : ℂ) else 0) := by
    intro bc'
    rw [show (∑ hostlab : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
          row hostlab •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A
                  (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) q = hostlab ∧
                  regionBoundaryLabel (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue q = bβ ∧
                    regionBoundaryLabel (G := G) A
                      (overlapRightGeometry (V := V) R₁ R₂).complement q = bc'
              then (1 : ℂ) else 0)) =
        ∑ b₂ : RegionBoundaryConfig (G := G) A R₂,
          overlapBridgeRow (G := G) (A := A) (cFiber (A := A) c δ) b₂ *
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A R₂ q = b₂ ∧
                  regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = bβ ∧
                    regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
              then (1 : ℂ) else 0) from ?_]
    · exact overlapBridge_coeff_eq (G := G) (A := A) (cFiber (A := A) c δ) bβ bc'
    · refine Fintype.sum_equiv (regionBoundaryConfigCongr (A := A) hHR) _ _ (fun hostlab => ?_)
      rw [hrow, smul_eq_mul]
      exact congrArg (overlapBridgeRow (G := G) (A := A) (cFiber (A := A) c δ)
          (regionBoundaryConfigCongr (A := A) hHR hostlab) * ·)
        (existsLabel_indicator_congr (A := A) hHR hostlab
          (fun q => regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = bβ ∧
            regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'))
  rw [Finset.sum_congr rfl (fun bc' _ => by rw [hcoeff bc', Finset.sum_smul])]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun β₁ _ => ?_)
  rw [Finset.sum_congr rfl (fun bc' _ => by rw [mul_smul]), ← Finset.smul_sum]
  have hstripzero := overlapLeft_firstStrip_fiber_weightCombination_eq_zero (G := G) (A := A)
      hR₁ c hc δ β₁ σcompl
  rw [(by exact hstripzero : (∑ x : RegionBoundaryConfig (G := G) A
          (overlapRightGeometry (V := V) R₁ R₂).complement,
        (∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
            cFiber (A := A) c δ bdry *
              (if ∃ q₂ : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₂ = bdry ∧
                    regionBoundaryLabel (G := G) A R₁ q₂ = β₁ ∧
                      regionBoundaryLabel (G := G) A (R₂ \ R₁) q₂ = x
                then (1 : ℂ) else 0)) •
          regionBlockedWeight (G := G) A (overlapRightGeometry (V := V) R₁ R₂).complement
            x σcompl) = 0), smul_zero]

/-! ### The `P₀`-fiber bridge row vanishes after inverting `R₂`

Feeding the fiber bridge to the right rebuild produces the interior-bond multiple of the
`δ`-fiber bridge row's combination of the `R₂` blocked weights, read through the fused
overlap/difference leg, equal to zero. The interior bond is positive, and the fused leg is
surjective onto the `R₂` physical configurations, so the combination is the zero blocked-region
tensor map of the row. Injectivity of `R₂` forces the `δ`-fiber bridge row to vanish. -/

open scoped Classical in
/-- **The `P₀`-fiber bridge row vanishes.** For `R₁`, `R₂` blocked-tensor injective, `c`
annihilating the host blocked weights, positive bond dimensions, and a reference `P₀`-outer label
`δ`, the `δ`-fiber bridge row `overlapBridgeRow (cFiber c δ)` is identically zero on the `R₂`
boundary configurations.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlapFiber_bridgeRow_eq_zero {R₁ R₂ : Finset V}
    (hR₁ : RegionBlockedTensorInjective (G := G) A R₁)
    (hR₂ : RegionBlockedTensorInjective (G := G) A R₂)
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red),
        (fun b => c (regionBoundaryConfigCongr (A := A)
            (overlapLeftGeometry_univ_sdiff_red R₁ R₂) b)) bdry •
          regionBlockedWeight (G := G) A
            (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) bdry = 0)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (δ : P0OuterConfig A R₁ R₂) :
    overlapBridgeRow (G := G) (A := A) (cFiber (A := A) c δ) = 0 := by
  classical
  set g := overlapRightGeometry (V := V) R₁ R₂ with hg
  have hHR : Finset.univ \ g.red = R₂ := overlapRightGeometry_univ_sdiff_red R₁ R₂
  -- The transported row over the geometry host.
  set row : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red) → ℂ :=
    fun b => overlapBridgeRow (G := G) (A := A) (cFiber (A := A) c δ)
      (regionBoundaryConfigCongr (A := A) hHR b) with hrowdef
  -- The fiber bridge gives the rebuild hypothesis for `row`.
  have hrowhyp : ∀ (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
      (bβ : RegionBoundaryConfig (G := G) A g.blue),
      ∑ bdry₂ : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
        row bdry₂ • g.threeBlockComplCoeff bdry₂ σcompl bβ = 0 := by
    intro σcompl bβ
    exact overlapFiber_bridge_rightCoupling_eq_zero (G := G) (A := A) hR₁ c hc hpos δ σcompl bβ
  -- Feed to the rebuild: the interior-bond scaled host-weight combination vanishes.
  have hrebuild := fun σblue σcompl =>
    overlapRight_bondProd_smul_hostWeight_combination_eq_zero (G := G) (A := A)
      (R₁ := R₁) (R₂ := R₂)
      row hrowhyp σblue σcompl
  -- interior bond positive ⟹ host-weight combination vanishes through complPhysical.
  have hintne : (regionInteriorBondProd (G := G) A g.blue : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (regionInteriorBondProd_pos (G := G) A g.blue hpos).ne'
  have hcomb : ∀ σblue σcompl,
      ∑ bdry₂ : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
        row bdry₂ • regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry₂
          (g.complPhysical σblue σcompl) = 0 := by
    intro σblue σcompl
    have := hrebuild σblue σcompl
    rwa [smul_eq_zero, or_iff_right hintne] at this
  -- Every R₂-physical config is complPhysical of some (σblue, σcompl); so the
  -- weight-combination (as a function on R₂ physical configs) vanishes.
  have hfun : (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ g.red) =>
      ∑ bdry₂ : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
        row bdry₂ • regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry₂ τ) = 0 := by
    funext τ
    obtain ⟨⟨σblue, σcompl⟩, hτ⟩ := g.complPhysical_surjective (d := d) τ
    rw [Pi.zero_apply, ← hτ]
    exact hcomb σblue σcompl
  -- This is `regionBlockedTensorMap (univ \ g.red) row = 0`; inject to `row = 0`.
  have hmap : regionBlockedTensorMap (G := G) A (Finset.univ \ g.red) row = 0 := by
    funext τ
    rw [regionBlockedTensorMap_apply, Pi.zero_apply]
    exact congrFun hfun τ
  have hR₂host : RegionBlockedTensorInjective (G := G) A (Finset.univ \ g.red) := by
    rw [hHR]; exact hR₂
  have hrow0 : row = 0 :=
    regionBlockedTensorMap_injective_of_injective (G := G) A (Finset.univ \ g.red) hR₂host
      (by rw [hmap, map_zero])
  -- Transport back: `overlapBridgeRow (cFiber c δ) = 0` over R₂.
  funext b₂
  have := congrFun hrow0 (regionBoundaryConfigCongr (A := A) hHR |>.symm b₂)
  rw [hrowdef] at this
  simp only [Pi.zero_apply] at this ⊢
  rwa [Equiv.apply_symm_apply] at this

/-! ### The final extraction: the union of two injective regions is injective

The fiber bridge row vanishes for every reference `P₀`-outer label. To extract a host coefficient,
realize the host label by a configuration `q₀`, take the reference `δ` to be the `P₀`-outer label of
`q₀` and `b₂` to be its `R₂` boundary label, and read the fiber bridge row at `b₂`. The surviving
term is the host label itself: any configuration realizing `b₂` with `P₀`-outer label `δ` has the
same union host label as `q₀` by the partition determinacy, so the fiber coefficient at the host
label is forced to vanish. -/

set_option linter.unusedSectionVars false in
omit [DecidableEq V] in
open scoped Classical in
/-- Transport of host annihilation along a region-set equality: if a coefficient family `c`
annihilates the blocked weights of `R`, then its transport annihilates the blocked weights of an
equal region `S`. This carries the natural `R₁ ∪ R₂` annihilation hypothesis to the
geometry-native host description the strip and bridge consume. -/
theorem hc_transport {S R : Finset V} (h : S = R)
    (c : RegionBoundaryConfig (G := G) A R → ℂ)
    (hc0 : ∑ bdry : RegionBoundaryConfig (G := G) A R,
      c bdry • regionBlockedWeight (G := G) A R bdry = 0) :
    ∑ bdry : RegionBoundaryConfig (G := G) A S,
      (fun b => c (regionBoundaryConfigCongr (A := A) h b)) bdry •
        regionBlockedWeight (G := G) A S bdry = 0 := by
  subst h
  rw [← hc0]
  refine Fintype.sum_equiv (regionBoundaryConfigCongr (A := A) rfl) _ _ (fun b => ?_)
  have hb : regionBoundaryConfigCongr (A := A) (rfl : S = S) b = b := by
    funext f; rw [regionBoundaryConfigCongr_apply]
  simp only []
  rw [hb]

set_option linter.unusedSectionVars false in
omit [Fintype V] in
open scoped Classical in
/-- **Union host-boundary surjectivity.** With positive bond dimensions, every union `R₁ ∪ R₂`
boundary configuration is the union boundary label of some global virtual configuration: read the
prescribed configuration on the boundary edges and an arbitrary index elsewhere.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_regionBoundaryLabel_union_eq {R₁ R₂ : Finset V}
    (bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂))
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    ∃ q : VirtualConfig A, regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry := by
  classical
  refine ⟨fun e => if h : IsRegionBoundaryEdge (G := G) (R₁ ∪ R₂) e then bdry ⟨e, h⟩
    else ⟨0, hpos e⟩, ?_⟩
  funext f
  rw [regionBoundaryLabel_apply, dif_pos f.2]

open scoped Classical in
/-- **The overlapping union-of-injective-regions lemma.** For two finite regions `R₁`, `R₂` whose
blocked tensors are injective, and with every virtual bond dimension positive, the blocked tensor
of their union `R₁ ∪ R₂` is injective. This removes the disjointness restriction of
`regionBlockedTensorInjective_union_disjoint`, completing the source's `injective_union`.

A coefficient family `c` annihilating the union blocked weights is first transported to the
left-geometry host. Inverting `R₁` (the first strip) frees the `R₁` boundary; re-inserting the
overlap `R₁ ∩ R₂` and inverting `R₂` (the right rebuild) would lose the `P₀`-outer host indices, so
the rebuild row is fed the coefficient family restricted to the `P₀`-fiber of a reference
`P₀`-outer label `δ`. The fiber-restricted first strip still vanishes, so the fiber bridge row
vanishes after inverting `R₂`. Evaluating it at the reference and at the `R₂` boundary label of a
realizing configuration selects, by the partition of the union boundary into `R₂` boundary edges
and `P₀`-outer edges, the single host term, forcing `c` to vanish at every realizable host label.
Union host-boundary surjectivity covers every label.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_union_overlap {R₁ R₂ : Finset V}
    (hR₁ : RegionBlockedTensorInjective (G := G) A R₁)
    (hR₂ : RegionBlockedTensorInjective (G := G) A R₂)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) :
    RegionBlockedTensorInjective (G := G) A (R₁ ∪ R₂) := by
  classical
  rw [RegionBlockedTensorInjective, Fintype.linearIndependent_iff]
  intro c hc
  have hc0 : ∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
      c bdry • regionBlockedWeight (G := G) A (R₁ ∪ R₂) bdry = 0 := hc
  have hcL := hc_transport (overlapLeftGeometry_univ_sdiff_red R₁ R₂) c hc0
  -- Extract `c` at every host label.
  intro bdry₀
  obtain ⟨q₀, hq₀⟩ := exists_regionBoundaryLabel_union_eq (A := A) bdry₀ hpos
  -- The fiber bridge row at δ := p0OuterLabel q₀ vanishes.
  have hrow0 := overlapFiber_bridgeRow_eq_zero (G := G) (A := A) hR₁ hR₂ c hcL hpos
    (p0OuterLabel A R₁ R₂ q₀)
  -- Evaluate the row at b₂ := R₂-label of q₀.
  have hrow0b := congrFun hrow0 (regionBoundaryLabel (G := G) A R₂ q₀)
  simp only [Pi.zero_apply, overlapBridgeRow] at hrow0b
  -- The single surviving term is `bdry = bdry₀ = union q₀`.
  rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₀)] at hrow0b
  · -- The surviving term: cFiber at union q₀ = c at union q₀ (fiber matches), indicator = 1.
    have hfiber : cFiber (A := A) c (p0OuterLabel A R₁ R₂ q₀)
        (regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₀) =
        c (regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₀) := by
      rw [cFiber, if_pos]
      rw [unionToP0Outer_regionBoundaryLabel]
    rw [hfiber, if_pos ⟨q₀, rfl, rfl⟩, smul_eq_mul, mul_one] at hrow0b
    rw [← hq₀]; exact hrow0b
  · -- Other `bdry`: either fiber mismatch or no joint realization.
    intro bdry _ hne
    by_cases hreal : ∃ q : VirtualConfig A,
        regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
          regionBoundaryLabel (G := G) A R₂ q = regionBoundaryLabel (G := G) A R₂ q₀
    · obtain ⟨q, hqu, hqr⟩ := hreal
      by_cases hfib : unionToP0Outer (A := A) bdry = p0OuterLabel A R₁ R₂ q₀
      · -- Both fiber and joint hold: then bdry = union q₀ by partition determinacy. Contradiction.
        exfalso
        apply hne
        rw [← hqu]
        have hδq : p0OuterLabel A R₁ R₂ q = p0OuterLabel A R₁ R₂ q₀ := by
          rw [← unionToP0Outer_regionBoundaryLabel, hqu]; exact hfib
        exact regionBoundaryLabel_union_eq_of_R₂_p0Outer (G := G) hqr hδq
      · rw [cFiber, if_neg hfib, zero_smul]
    · rw [if_neg hreal, smul_zero]
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

end PEPS
end TNLean
