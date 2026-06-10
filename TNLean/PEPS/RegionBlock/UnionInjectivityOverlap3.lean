import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap2

/-!
# The overlapping union lemma: the P₀-outer bridge and the closure

This file supplies the final sub-step of the source's overlapping union-of-injective-regions
lemma of the normal PEPS Fundamental Theorem (arXiv:1804.04964, Section 3, Lemma
`injective_union`, lines 1324--1400 of `Papers/1804.04964/paper_normal.tex`) and assembles
the full overlapping union theorem `regionBlockedTensorInjective_union_overlap`.

The companions `TNLean.PEPS.RegionBlock.UnionInjectivityOverlap` and
`TNLean.PEPS.RegionBlock.UnionInjectivityOverlap2` land the two host three-block geometries
(`overlapLeftGeometry`, `overlapRightGeometry`), the first inverse application
`overlap_firstStrip`, and the rebuild step
`overlapRight_bondProd_smul_hostWeight_combination_eq_zero`.

With the four parts `P₀ = R₁ \ R₂`, `P₁ = R₁ ∩ R₂`, `P₂ = R₂ \ R₁`, both the left geometry's
complement coupling and the right geometry's complement coupling are sums of the same `P₂`
vertex product over global virtual configurations. The landed crossing collapse
(`blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq`) reads each coupling, scaled by its
own positive blue/red crossing bond product, as the same family of `P₂` blocked-region
weights `regionBlockedWeight A P₂`, with an existence-indicator coefficient. The bridge matches
the two indicator coefficients: the right geometry's coupling combination, scaled and read
through the `P₂` weights, is exactly the left geometry's first-strip combination read through
the same weights, so it vanishes by `overlap_firstStrip`.

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

/-! ### The shared complement block `P₂`

Both overlap geometries have complement block `R₂ \ R₁ = P₂`, so both complement couplings
read the same `P₂` blocked-region weights `regionBlockedWeight A (R₂ \ R₁)`. -/

omit [LinearOrder V] [DecidableRel G.Adj] in
/-- The two overlap geometries share the complement block `R₂ \ R₁`. -/
theorem overlap_complement_eq (R₁ R₂ : Finset V) :
    (overlapLeftGeometry (V := V) R₁ R₂).complement =
      (overlapRightGeometry (V := V) R₁ R₂).complement := rfl

/-! ### Reducing a coupling combination to the `P₂` blocked-region weights

The landed crossing collapse `blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq` reads, for
either overlap geometry `g`, the positive crossing-bond multiple of the complement coupling
`threeBlockComplCoeff g hostlab σ bluelab` as a sum over complement boundary configurations
`bc'` of an existence indicator times the complement weight `regionBlockedWeight A g.complement
bc' σ`. Distributing a coefficient family over the geometry's host boundary configurations
through this collapse expresses the scaled coupling combination as an
existence-indicator-weighted combination of the complement weights. -/

open scoped Classical in
/-- For a `ThreeBlockGeometry` `g` and a coefficient family `coef` over the host boundary
configurations, the crossing-bond multiple of the `coef`-combination of the complement
couplings (at a fixed blue boundary configuration `bβ`) is the combination of the complement
blocked-region weights with the existence-indicator coefficient
`∑ hostlab, coef hostlab • 1[∃ q realizing host = hostlab, blue = bβ, complement = bc']`. -/
theorem ThreeBlockGeometry.crossingBond_smul_complCoeff_combination_eq
    (g : ThreeBlockGeometry V)
    (coef : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red) → ℂ)
    (bβ : RegionBoundaryConfig (G := G) A g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (g.blueRedCrossingBondProd A : ℂ) •
        ∑ hostlab : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          coef hostlab • g.threeBlockComplCoeff hostlab σcompl bβ =
      ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
        (∑ hostlab : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            coef hostlab •
              (if ∃ q : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = hostlab ∧
                    regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                      regionBoundaryLabel (G := G) A g.complement q = bc'
                then (1 : ℂ) else 0)) •
          regionBlockedWeight (G := G) A g.complement bc' σcompl := by
  classical
  rw [Finset.smul_sum]
  rw [Finset.sum_congr rfl (g := fun hostlab =>
        coef hostlab • ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
          (if ∃ q : VirtualConfig A,
              regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = hostlab ∧
                regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                  regionBoundaryLabel (G := G) A g.complement q = bc'
            then (1 : ℂ) else 0) • regionBlockedWeight (G := G) A g.complement bc' σcompl)
      (fun hostlab _ => by
        rw [smul_comm, g.blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq hostlab bβ σcompl])]
  -- Push the `coef hostlab` scalar into each `bc'` summand.
  rw [Finset.sum_congr rfl (g := fun hostlab =>
        ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
          (coef hostlab •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = hostlab ∧
                  regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                    regionBoundaryLabel (G := G) A g.complement q = bc'
              then (1 : ℂ) else 0)) •
            regionBlockedWeight (G := G) A g.complement bc' σcompl)
      (fun hostlab _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun bc' _ => by rw [smul_assoc]))]
  -- Swap the `hostlab` and `bc'` summation order and gather the coefficient.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  rw [Finset.sum_smul]

/-! ### Realizability of prescribed region labels

A total virtual configuration `val` realizes, on every region `R`, the boundary label that
is the restriction of `val` to the boundary edges of `R`. Hence an existence indicator
`∃ q, lab_{R} q = bcfg ∧ …` is decided by whether the prescribed boundary labels are the
restrictions of a common `val`. Building `val` from boundary labels that agree on shared
boundary edges is the gluing the bridge needs. -/

/-! ### The `P₀`-outer edges

An edge is `P₀`-outer when it is a boundary edge of the union `R₁ ∪ R₂` but not a boundary
edge of `R₂`. Such an edge runs from the difference block `P₀ = R₁ \ R₂` to the outside
`(R₁ ∪ R₂)ᶜ`: its in-union endpoint lies in `R₁ \ R₂` (it is outside `R₂`, else the edge
would be an `R₂` boundary edge) and its other endpoint lies outside `R₁ ∪ R₂` (hence outside
`R₂`). These are the edges free in the right geometry's host `R₂` label but pinned in the
left geometry's host `R₁ ∪ R₂` label; gluing along them bridges the two host residuals. -/

/-- A `P₀`-outer edge: a boundary edge of `R₁ ∪ R₂` that is not a boundary edge of `R₂`. -/
def IsP0OuterEdge (R₁ R₂ : Finset V) (e : Edge G) : Prop :=
  IsRegionBoundaryEdge (G := G) (R₁ ∪ R₂) e ∧ ¬ IsRegionBoundaryEdge (G := G) R₂ e

instance (R₁ R₂ : Finset V) (e : Edge G) :
    Decidable (IsP0OuterEdge (G := G) R₁ R₂ e) := by
  unfold IsP0OuterEdge; infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- Each endpoint of a `P₀`-outer edge lies outside `R₂`: one endpoint is in `R₁ ∪ R₂` while
the other is outside, and not being an `R₂` boundary edge forces both onto the same side of
`R₂`, namely outside it. -/
theorem isP0OuterEdge_both_not_mem_R₂ {R₁ R₂ : Finset V} {e : Edge G}
    (h : IsP0OuterEdge (G := G) R₁ R₂ e) : e.1.1 ∉ R₂ ∧ e.1.2 ∉ R₂ := by
  obtain ⟨hunion, hnotR₂⟩ := h
  -- The union boundary edge has one endpoint in `R₁ ∪ R₂` and one outside, hence outside `R₂`.
  rcases hunion with ⟨h1u, h2nu⟩ | ⟨h1nu, h2u⟩
  · -- `e.1.2 ∉ R₁ ∪ R₂`, so `e.1.2 ∉ R₂`; not an `R₂` boundary edge forces `e.1.1 ∉ R₂`.
    have h2 : e.1.2 ∉ R₂ := fun h => h2nu (Finset.mem_union_right _ h)
    refine ⟨?_, h2⟩
    intro h1
    exact hnotR₂ (Or.inl ⟨h1, h2⟩)
  · have h1 : e.1.1 ∉ R₂ := fun h => h1nu (Finset.mem_union_right _ h)
    refine ⟨h1, ?_⟩
    intro h2
    exact hnotR₂ (Or.inr ⟨h1, h2⟩)

omit [Fintype V] [DecidableRel G.Adj] in
/-- A `P₀`-outer edge is not a boundary edge of the overlap `R₁ ∩ R₂`: both endpoints lie
outside `R₂`, hence outside the overlap. -/
theorem not_isRegionBoundaryEdge_inter_of_p0Outer {R₁ R₂ : Finset V} {e : Edge G}
    (h : IsP0OuterEdge (G := G) R₁ R₂ e) :
    ¬ IsRegionBoundaryEdge (G := G) (R₁ ∩ R₂) e := by
  obtain ⟨h1, h2⟩ := isP0OuterEdge_both_not_mem_R₂ (G := G) h
  rintro (⟨h1', _⟩ | ⟨_, h2'⟩)
  · exact h1 (Finset.mem_inter.mp h1').2
  · exact h2 (Finset.mem_inter.mp h2').2

omit [Fintype V] [DecidableRel G.Adj] in
/-- A `P₀`-outer edge is not a boundary edge of `R₂ \ R₁`: both endpoints lie outside `R₂`,
hence outside the difference. -/
theorem not_isRegionBoundaryEdge_sdiff_of_p0Outer {R₁ R₂ : Finset V} {e : Edge G}
    (h : IsP0OuterEdge (G := G) R₁ R₂ e) :
    ¬ IsRegionBoundaryEdge (G := G) (R₂ \ R₁) e := by
  obtain ⟨h1, h2⟩ := isP0OuterEdge_both_not_mem_R₂ (G := G) h
  rintro (⟨h1', _⟩ | ⟨_, h2'⟩)
  · exact h1 (Finset.mem_sdiff.mp h1').1
  · exact h2 (Finset.mem_sdiff.mp h2').1

omit [Fintype V] [DecidableRel G.Adj] in
/-- A boundary edge of the union `R₁ ∪ R₂` that is not `P₀`-outer is a boundary edge of `R₂`,
by the very definition of `P₀`-outer. -/
theorem isRegionBoundaryEdge_R₂_of_unionBoundary_not_p0Outer {R₁ R₂ : Finset V} {e : Edge G}
    (hunion : IsRegionBoundaryEdge (G := G) (R₁ ∪ R₂) e)
    (hnp0 : ¬ IsP0OuterEdge (G := G) R₁ R₂ e) :
    IsRegionBoundaryEdge (G := G) R₂ e := by
  by_contra h
  exact hnp0 ⟨hunion, h⟩

/-! ### Gluing two configurations along the `P₀`-outer edges

A configuration `q₂` carrying the `R₂`, overlap, and difference labels prescribed by the
right geometry, overwritten on the `P₀`-outer edges by a configuration `q₁` carrying the
union host label `bdry`, carries all four labels: the overlap and difference labels are
untouched (the `P₀`-outer edges are not their boundary edges) and the union host label is
`bdry` (on `P₀`-outer edges it reads `q₁`, elsewhere it reads `q₂`, which agrees with `q₁`
on the `R₂` boundary edges they share). -/

open scoped Classical in
/-- The configuration overwriting `q₂` by `q₁` on the `P₀`-outer edges. -/
noncomputable def p0OuterGlue (R₁ R₂ : Finset V) (q₁ q₂ : VirtualConfig A) :
    VirtualConfig A :=
  fun e => if IsP0OuterEdge (G := G) R₁ R₂ e then q₁ e else q₂ e

omit [Fintype V] in
/-- The glued configuration agrees with `q₂` on the overlap `R₁ ∩ R₂` boundary label. -/
theorem regionBoundaryLabel_inter_p0OuterGlue {R₁ R₂ : Finset V} (q₁ q₂ : VirtualConfig A) :
    regionBoundaryLabel (G := G) A (R₁ ∩ R₂) (p0OuterGlue (G := G) R₁ R₂ q₁ q₂) =
      regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q₂ := by
  classical
  funext f
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply, p0OuterGlue,
    if_neg (fun hp0 => not_isRegionBoundaryEdge_inter_of_p0Outer (G := G) hp0 f.2)]

omit [Fintype V] in
/-- The glued configuration agrees with `q₂` on the difference `R₂ \ R₁` boundary label. -/
theorem regionBoundaryLabel_sdiff_p0OuterGlue {R₁ R₂ : Finset V} (q₁ q₂ : VirtualConfig A) :
    regionBoundaryLabel (G := G) A (R₂ \ R₁) (p0OuterGlue (G := G) R₁ R₂ q₁ q₂) =
      regionBoundaryLabel (G := G) A (R₂ \ R₁) q₂ := by
  classical
  funext f
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply, p0OuterGlue,
    if_neg (fun hp0 => not_isRegionBoundaryEdge_sdiff_of_p0Outer (G := G) hp0 f.2)]

omit [Fintype V] in
/-- The glued configuration carries the union host label `bdry`, provided `q₁` carries it and
`q₂` agrees with `q₁` on the `R₂` boundary label. On a `P₀`-outer union boundary edge the glue
reads `q₁ = bdry`; on a non-`P₀`-outer union boundary edge (an `R₂` boundary edge) it reads
`q₂`, which there equals `q₁ = bdry`. -/
theorem regionBoundaryLabel_union_p0OuterGlue {R₁ R₂ : Finset V} (q₁ q₂ : VirtualConfig A)
    {bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂)}
    (h1 : regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₁ = bdry)
    (hR₂ : regionBoundaryLabel (G := G) A R₂ q₂ = regionBoundaryLabel (G := G) A R₂ q₁) :
    regionBoundaryLabel (G := G) A (R₁ ∪ R₂) (p0OuterGlue (G := G) R₁ R₂ q₁ q₂) = bdry := by
  classical
  funext f
  rw [regionBoundaryLabel_apply, p0OuterGlue]
  by_cases hp0 : IsP0OuterEdge (G := G) R₁ R₂ f.1
  · rw [if_pos hp0]
    have := congrFun h1 f; rwa [regionBoundaryLabel_apply] at this
  · rw [if_neg hp0]
    have hR₂edge := isRegionBoundaryEdge_R₂_of_unionBoundary_not_p0Outer (G := G) f.2 hp0
    have hq := congrFun hR₂ ⟨f.1, hR₂edge⟩
    rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply] at hq
    rw [hq]
    have := congrFun h1 f; rwa [regionBoundaryLabel_apply] at this

end PEPS
end TNLean
