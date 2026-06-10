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

end PEPS
end TNLean
