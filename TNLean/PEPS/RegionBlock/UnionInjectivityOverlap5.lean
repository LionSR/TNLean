import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap4

/-!
# The overlapping union lemma: the host-spanning rebuild and the closure

This file closes the source's overlapping union-of-injective-regions lemma of the normal PEPS
Fundamental Theorem (arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`). The companions `UnionInjectivityOverlap`, `2`, `3`, and `4`
land the two host three-block geometries, the first inverse application `overlap_firstStrip`, the
right-geometry blue-side rebuild, the `P₀`-outer bridge, and the host/difference reconstruction
together with the overlap-crossing multiplicity collapse.

The closure recorded in obligation 1 of `docs/paper-gaps/peps_normal_ft_section3_route.tex`
requires a rebuild whose row spans the full host `R₁ ∪ R₂` boundary, so that the open-`R₁`-legs
configuration `β₁` can be carried alongside the `R₂` boundary. This file supplies it. Fixing
`β₁`, the row over `R₂` boundary configurations is
`b₂ ↦ ∑ bdry, c(bdry) • 1[∃ q : union = bdry ∧ R₁ = β₁ ∧ R₂ = b₂]`. Its right-coupling
combination, via the right-geometry crossing collapse, is the `β₁`-aware bridge: the
overlap-glue indicator over (`R₁`, overlap) times the `β₁`-restricted first-strip combination,
which vanishes by `overlapLeft_firstStrip_weightCombination_eq_zero` at `β₁`. The rebuild then
produces a vanishing combination of the `R₂` blocked weights, the left inverse for `R₂` forces
the row to vanish, and host reconstruction from the pair (`β₁`, `R₂`-boundary) makes the final
extraction a single-term selection forcing `c = 0` at every realizable host label. Host-boundary
surjectivity covers every label.

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

/-! ### Transport of physical configurations, weights, and injectivity along region equality

The right-geometry rebuild produces a vanishing combination of the blocked weights of the
geometry-native host `univ \ red`, which is the literal region `R₂`. To feed the combination
to the left inverse for `R₂`, the weight is transported along the region-set equality
`univ \ red = R₂`, mirroring the boundary-configuration transport `regionBoundaryConfigCongr`.
-/

/-- The transport equivalence of physical configurations along a region-set equality: relabel
the vertex index along the equality of regions. -/
def regionPhysicalConfigCongr {S R : Finset V} (h : S = R) :
    RegionPhysicalConfig (V := V) (d := d) S ≃ RegionPhysicalConfig (V := V) (d := d) R :=
  Equiv.piCongrLeft' _ (Equiv.subtypeEquivRight (fun _ => by rw [h]))

omit [Fintype V] [DecidableEq V] [LinearOrder V] [DecidableRel G.Adj] in
/-- The transported physical configuration reads the same value as the original on a vertex. -/
theorem regionPhysicalConfigCongr_apply {S R : Finset V} (h : S = R)
    (τ : RegionPhysicalConfig (V := V) (d := d) S) (w : {w : V // w ∈ R}) :
    regionPhysicalConfigCongr (d := d) h τ w = τ ⟨w.1, by rw [h]; exact w.2⟩ := rfl

omit [DecidableEq V] in
/-- The blocked-region weight transports along a region-set equality: for equal regions the
weight of a configuration agrees with the weight of its transported boundary and physical
configurations. -/
theorem regionBlockedWeight_congr {S R : Finset V} (h : S = R)
    (bdry : RegionBoundaryConfig (G := G) A S)
    (τ : RegionPhysicalConfig (V := V) (d := d) S) :
    regionBlockedWeight (G := G) A S bdry τ =
      regionBlockedWeight (G := G) A R
        (regionBoundaryConfigCongr (A := A) h bdry)
        (regionPhysicalConfigCongr (d := d) h τ) := by
  subst h
  rfl

/-! ### Surjectivity of the fused complement physical leg

The fused leg `complPhysical σblue σcompl` ranges over every physical configuration of the host
`univ \ red` as the blue and complement legs vary: a host vertex lies in exactly one of the blue
and complement blocks (the red block is disjoint from the host), so reading the prescribed leg on
the blue block and on the complement block recovers it. -/

/-- The fused complement physical leg is surjective: every physical configuration of the host
`univ \ g.red` is `g.complPhysical σblue σcompl` for some blue and complement legs. -/
theorem ThreeBlockGeometry.complPhysical_surjective (g : ThreeBlockGeometry V) :
    Function.Surjective
      (fun p : RegionPhysicalConfig (V := V) (d := d) g.blue ×
          RegionPhysicalConfig (V := V) (d := d) g.complement =>
        g.complPhysical (d := d) p.1 p.2) := by
  classical
  intro τ
  refine ⟨⟨fun w => τ ⟨w.1, ?_⟩, fun w => τ ⟨w.1, ?_⟩⟩, ?_⟩
  · -- A blue vertex lies in the host `univ \ red`.
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, fun hr => (Finset.disjoint_left.mp g.red_disjoint_blue) hr w.2⟩
  · -- A complement vertex lies in the host `univ \ red`.
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, fun hr => (Finset.disjoint_left.mp g.red_disjoint_complement) hr w.2⟩
  · funext w
    simp only
    by_cases hb : w.1 ∈ g.blue
    · rw [g.complPhysical_apply_blue _ _ w hb]
    · -- A host vertex outside the blue block lies in the complement block.
      have hwnotred : w.1 ∉ g.red := (Finset.mem_sdiff.mp w.2).2
      have hc : w.1 ∈ g.complement := by
        have hcover : w.1 ∈ g.red ∪ g.blue ∪ g.complement := by
          rw [g.cover_univ]; exact Finset.mem_univ _
        rcases Finset.mem_union.mp hcover with hrb | hc
        · rcases Finset.mem_union.mp hrb with hr | hbl
          · exact absurd hr hwnotred
          · exact absurd hbl hb
        · exact hc
      rw [g.complPhysical_apply_not_blue _ _ w hb hc]

/-! ### The host three-block geometry over the host `R₁ ∪ R₂`

The `β₁`-aware rebuild reads the host `R₁ ∪ R₂` weight through the full host boundary, factoring
through `regionBlockedTensorMap A R₂`. The three-block geometry realizing this places `R₂` as the
blue block, the difference `R₁ \ R₂` as the complement block, and `(R₁ ∪ R₂)ᶜ` as the red block;
its host is `R₁ ∪ R₂`. The blue/complement crossings then run between `R₂` and `R₁ \ R₂`, the
edges the `R₂` boundary configuration does not see, so inverting the blue block `R₂` reads off the
coefficient row carrying the residual `R₁ \ R₂` data alongside the `R₂` boundary. -/

/-- The three-block geometry over the host `R₁ ∪ R₂` placing `R₂` as the blue block, the
difference `R₁ \ R₂` as the complement block, and `(R₁ ∪ R₂)ᶜ` as the red block.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
def overlapHostGeometry (R₁ R₂ : Finset V) : ThreeBlockGeometry V where
  red := Finset.univ \ (R₁ ∪ R₂)
  blue := R₂
  complement := R₁ \ R₂
  red_disjoint_blue := by
    rw [Finset.disjoint_left]
    intro v hv hvR₂
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ hvR₂)
  red_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hv hvc
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_union_left _ (Finset.mem_sdiff.mp hvc).1)
  blue_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hvR₂ hvc
    exact (Finset.mem_sdiff.mp hvc).2 hvR₂
  cover_univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    tauto

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapHostGeometry_blue (R₁ R₂ : Finset V) :
    (overlapHostGeometry (V := V) R₁ R₂).blue = R₂ := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapHostGeometry_complement (R₁ R₂ : Finset V) :
    (overlapHostGeometry (V := V) R₁ R₂).complement = R₁ \ R₂ := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapHostGeometry_red (R₁ R₂ : Finset V) :
    (overlapHostGeometry (V := V) R₁ R₂).red = Finset.univ \ (R₁ ∪ R₂) := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
/-- The host block of the host geometry is the union `R₁ ∪ R₂`. -/
theorem overlapHostGeometry_univ_sdiff_red (R₁ R₂ : Finset V) :
    Finset.univ \ (overlapHostGeometry (V := V) R₁ R₂).red = R₁ ∪ R₂ := by
  rw [overlapHostGeometry_red]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]

/-! ### The host-spanning rebuild: inverting the blue block `R₂`

Applying the generic blue strip `ThreeBlockGeometry.complCoeff_combination_eq_zero` to the host
geometry inverts its blue block `R₂`: a coefficient family `c` annihilating the host `R₁ ∪ R₂`
weights has its `c`-weighted host-geometry complement coupling vanish for every difference leg
`σcompl` over `R₁ \ R₂` and every `R₂` boundary configuration `b₂`. The complement coupling
couples the host boundary `bdry` to the `R₂` boundary `b₂` through the difference block `R₁ \ R₂`,
so the row carries the residual `R₁ \ R₂` data alongside the `R₂` boundary. -/

open scoped Classical in
/-- **The host-spanning rebuild (inverting `R₂`).** For a coefficient family `c` over the host
`R₁ ∪ R₂` boundary configurations annihilating the host blocked weights, and `R₂` blocked-tensor
injective, the `c`-weighted host-geometry complement coupling vanishes for every difference leg
`σcompl` over `R₁ \ R₂` and `R₂` boundary configuration `b₂`.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlapHost_complCoeff_combination_eq_zero {R₁ R₂ : Finset V}
    (hR₂ : RegionBlockedTensorInjective (G := G) A R₂)
    (c : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapHostGeometry (V := V) R₁ R₂).red) → ℂ)
    (hc : ∑ bdry, c bdry •
        regionBlockedWeight (G := G) A
          (Finset.univ \ (overlapHostGeometry (V := V) R₁ R₂).red) bdry = 0)
    (σcompl : RegionPhysicalConfig (V := V) (d := d)
        (overlapHostGeometry (V := V) R₁ R₂).complement)
    (b₂ : RegionBoundaryConfig (G := G) A (overlapHostGeometry (V := V) R₁ R₂).blue) :
    ∑ bdry, c bdry •
        (overlapHostGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry σcompl b₂ = 0 :=
  (overlapHostGeometry (V := V) R₁ R₂).complCoeff_combination_eq_zero
    (by rw [overlapHostGeometry_blue]; exact hR₂) c hc σcompl b₂

/-! ### The host complement coupling collapses onto the difference `R₁ \ R₂` weights

The host geometry's blue/red crossing-bond collapse expresses the `c`-weighted host complement
coupling as a combination of the difference `R₁ \ R₂` blocked weights, the coefficient at the
difference boundary configuration `b₀` being the `c`-sum over host residuals jointly realizable
with the `R₂` boundary `b₂` and the difference boundary `b₀`. Combined with the rebuild, this is
the host-spanning analogue of the left first strip's reduction to the `R₂ \ R₁` weights: the
vanishing host complement coupling, scaled by the positive crossing bond, reads the difference
weight combination as zero for every `R₂` boundary configuration `b₂`. -/

open scoped Classical in
/-- **The host-spanning difference-weight reduction.** For a coefficient family `c` over the host
`R₁ ∪ R₂` boundary configurations annihilating the host blocked weights, and `R₂` blocked-tensor
injective, the joint-indicator combination of the difference `R₁ \ R₂` blocked weights is zero for
every `R₂` boundary configuration `b₂`: the coefficient at the difference boundary `b₀` is the
`c`-sum over host residuals jointly realizable with `R₂ = b₂` and `R₁ \ R₂` boundary `= b₀`.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlapHost_differenceWeight_combination_eq_zero {R₁ R₂ : Finset V}
    (hR₂ : RegionBlockedTensorInjective (G := G) A R₂)
    (c : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapHostGeometry (V := V) R₁ R₂).red) → ℂ)
    (hc : ∑ bdry, c bdry •
        regionBlockedWeight (G := G) A
          (Finset.univ \ (overlapHostGeometry (V := V) R₁ R₂).red) bdry = 0)
    (b₂ : RegionBoundaryConfig (G := G) A (overlapHostGeometry (V := V) R₁ R₂).blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d)
        (overlapHostGeometry (V := V) R₁ R₂).complement) :
    ∑ b₀ : RegionBoundaryConfig (G := G) A (overlapHostGeometry (V := V) R₁ R₂).complement,
        (∑ bdry : RegionBoundaryConfig (G := G) A
            (Finset.univ \ (overlapHostGeometry (V := V) R₁ R₂).red),
            c bdry •
              (if ∃ q : VirtualConfig A,
                  regionBoundaryLabel (G := G) A
                    (Finset.univ \ (overlapHostGeometry (V := V) R₁ R₂).red) q = bdry ∧
                    regionBoundaryLabel (G := G) A (overlapHostGeometry (V := V) R₁ R₂).blue q
                      = b₂ ∧
                      regionBoundaryLabel (G := G) A
                        (overlapHostGeometry (V := V) R₁ R₂).complement q = b₀
                then (1 : ℂ) else 0)) •
          regionBlockedWeight (G := G) A
            (overlapHostGeometry (V := V) R₁ R₂).complement b₀ σcompl = 0 := by
  classical
  -- The crossing collapse expresses the scaled `c`-coupling through the difference weights.
  have hcollapse := (overlapHostGeometry (V := V) R₁ R₂).crossingBond_smul_complCoeff_combination_eq
    (A := A) c b₂ σcompl
  -- The rebuild kills the left-hand side of the collapse, so the right-hand side is zero.
  rw [overlapHost_complCoeff_combination_eq_zero hR₂ c hc σcompl b₂, smul_zero] at hcollapse
  exact hcollapse.symm

/-! ### Host reconstruction from the `R₂` and difference `R₁ \ R₂` labels

Every boundary edge of the union `R₁ ∪ R₂` is a boundary edge of `R₂` or of the difference
`R₁ \ R₂`: its in-union endpoint lies in `R₂` (an `R₂` boundary edge) or in `R₁ \ R₂` (a
difference boundary edge), while its out endpoint lies outside `R₁ ∪ R₂`, hence outside both.
Therefore the union host boundary label is determined by the `R₂` and `R₁ \ R₂` boundary labels.
This is the host reconstruction underlying the host-spanning final extraction: the pair
(`R₂`-boundary, `R₁ \ R₂`-boundary) is the host geometry's (blue, complement) pair, and it
determines the host residual the rebuilt coefficient lives on. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- A boundary edge of the union `R₁ ∪ R₂` is a boundary edge of `R₂` or of the difference
`R₁ \ R₂`. -/
theorem isRegionBoundaryEdge_R₂_or_sdiff_of_union {R₁ R₂ : Finset V} {e : Edge G}
    (h : IsRegionBoundaryEdge (G := G) (R₁ ∪ R₂) e) :
    IsRegionBoundaryEdge (G := G) R₂ e ∨ IsRegionBoundaryEdge (G := G) (R₁ \ R₂) e := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `e.1.1 ∈ R₁ ∪ R₂`, `e.1.2 ∉ R₁ ∪ R₂`; the out endpoint is outside `R₂` and `R₁ \ R₂`.
    have h2R₂ : e.1.2 ∉ R₂ := fun h => h2 (Finset.mem_union_right _ h)
    have h2sd : e.1.2 ∉ R₁ \ R₂ := fun h => h2 (Finset.mem_union_left _ (Finset.mem_sdiff.mp h).1)
    by_cases hb : e.1.1 ∈ R₂
    · exact Or.inl (Or.inl ⟨hb, h2R₂⟩)
    · -- `e.1.1 ∈ R₁ ∪ R₂` and `∉ R₂` forces `e.1.1 ∈ R₁ \ R₂`.
      exact Or.inr
        (Or.inl ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp h1).resolve_right hb, hb⟩, h2sd⟩)
  · have h1R₂ : e.1.1 ∉ R₂ := fun h => h1 (Finset.mem_union_right _ h)
    have h1sd : e.1.1 ∉ R₁ \ R₂ := fun h => h1 (Finset.mem_union_left _ (Finset.mem_sdiff.mp h).1)
    by_cases hb : e.1.2 ∈ R₂
    · exact Or.inl (Or.inr ⟨h1R₂, hb⟩)
    · exact Or.inr
        (Or.inr ⟨h1sd, Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp h2).resolve_right hb, hb⟩⟩)

omit [Fintype V] in
/-- The union host boundary label is determined by the `R₂` and difference `R₁ \ R₂` boundary
labels: if two configurations share their `R₂` and `R₁ \ R₂` labels, they share their
`R₁ ∪ R₂` label. -/
theorem regionBoundaryLabel_union_eq_of_R₂_sdiff {R₁ R₂ : Finset V} {q q' : VirtualConfig A}
    (hR₂ : regionBoundaryLabel (G := G) A R₂ q = regionBoundaryLabel (G := G) A R₂ q')
    (hsd : regionBoundaryLabel (G := G) A (R₁ \ R₂) q =
      regionBoundaryLabel (G := G) A (R₁ \ R₂) q') :
    regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q' := by
  funext f
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply]
  rcases isRegionBoundaryEdge_R₂_or_sdiff_of_union (G := G) f.2 with he | he
  · have := congrFun hR₂ ⟨f.1, he⟩; rwa [regionBoundaryLabel_apply,
      regionBoundaryLabel_apply] at this
  · have := congrFun hsd ⟨f.1, he⟩; rwa [regionBoundaryLabel_apply,
      regionBoundaryLabel_apply] at this

/-! ### The host-residual coefficient is selected by the `R₂` and difference labels

Because the union host boundary label is determined by the pair (`R₂`-boundary, `R₁ \ R₂`-boundary)
(`regionBoundaryLabel_union_eq_of_R₂_sdiff`), the `c`-sum over host residuals jointly realizable
with `R₂ = b₂` and `R₁ \ R₂` boundary `= b₀` selects a single term: the coefficient `c` at the
unique host residual carried by a realizing configuration. This turns the difference-weight
reduction's coefficient into a single `c` value, so its vanishing is exactly `c = 0` at every
realizable host label. -/

open scoped Classical in
/-- The host-residual selection: for a global configuration `q`, the `c`-sum over host residuals
jointly realizable with the `R₂` and `R₁ \ R₂` labels of `q` selects `c` at the host label of
`q`. Two configurations realizing the same `R₂` and `R₁ \ R₂` labels share their union host label,
so the joint indicator is nonzero only at the host label of `q`. -/
theorem overlapHost_coeff_select {R₁ R₂ : Finset V}
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ) (q : VirtualConfig A) :
    ∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
        c bdry •
          (if ∃ q' : VirtualConfig A,
              regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q' = bdry ∧
                regionBoundaryLabel (G := G) A R₂ q' = regionBoundaryLabel (G := G) A R₂ q ∧
                  regionBoundaryLabel (G := G) A (R₁ \ R₂) q' =
                    regionBoundaryLabel (G := G) A (R₁ \ R₂) q
            then (1 : ℂ) else 0) =
      c (regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q) := by
  classical
  rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q)]
  · rw [if_pos ⟨q, rfl, rfl, rfl⟩, smul_eq_mul, mul_one]
  · intro bdry' _ hne
    -- Any configuration realizing `q`'s `R₂` and `R₁ \ R₂` labels has union host label `host q`.
    rw [if_neg ?_, smul_zero]
    rintro ⟨q', hu', hR₂', hsd'⟩
    exact hne (hu'.symm.trans (regionBoundaryLabel_union_eq_of_R₂_sdiff (G := G) hR₂' hsd'))
  · intro h; exact absurd (Finset.mem_univ _) h

end PEPS
end TNLean
