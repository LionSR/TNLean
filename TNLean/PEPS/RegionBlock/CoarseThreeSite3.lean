import TNLean.PEPS.RegionBlock.CoarseThreeSite2
import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral

/-!
# The three-region merge collapse for the normal PEPS theorem

The coarse three-site tensor of `TNLean.PEPS.RegionBlock.CoarseThreeSite` has its
closed-state coefficient written, through the coherent bond models of
`TNLean.PEPS.RegionBlock.CoarseThreeSite2`, as a sum over coarse virtual
configurations of a product of three original blocked-region weights
(`stateCoeff_coarseTensor_eq_threeRegionSum`). This file collapses that triple
sum to a constant times the original closed-state coefficient, the merge collapse
that glues the coarse state to the original state.

The route fuses the blue and complement weights into the host weight over
`univ \ red` and then applies the landed two-block collapse
`stateCoeff_eq_regionComplement` of `TNLean.PEPS.RegionBlock.Recovery` for the red
region against its set complement. The constants are the interior bond products of
the three regions, all positive under positive bond dimensions.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1205--1210 (the one-region-against-complement gluing) and
  1449--1500 (the blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The partition hypothesis of a coarse blocking frame

The merge collapse needs the three regions to partition the vertex set: the red,
blue, and complement regions are pairwise disjoint and cover `V`. A
`CoarseBlockingFrame` records only the three region injectivities, so the
partition is supplied as a separate hypothesis bundle. It is the geometry of the
source's edge blocking (arXiv:1804.04964, Section 3, the three injective regions
of a `NormalEdgeBlockingData` partition the lattice), here detached from the
tensor construction so the collapse reads only the partition. -/

namespace CoarseBlockingFrame

variable {A : Tensor G d} (F : CoarseBlockingFrame (G := G) (d := d) A)

/-- **The partition of a coarse blocking frame.** The red, blue, and complement
regions are pairwise disjoint and cover the vertex set. This is the geometry of
the source's edge blocking (arXiv:1804.04964, Section 3, proof of Theorem 3, the
three injective regions partition the lattice).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
structure IsPartition : Prop where
  /-- The red and blue regions are disjoint. -/
  red_disjoint_blue : Disjoint F.red F.blue
  /-- The red and complement regions are disjoint. -/
  red_disjoint_complement : Disjoint F.red F.complement
  /-- The blue and complement regions are disjoint. -/
  blue_disjoint_complement : Disjoint F.blue F.complement
  /-- The three regions cover the vertex set. -/
  cover_univ : F.red ∪ F.blue ∪ F.complement = Finset.univ

namespace IsPartition

variable {F}

/-- The set complement of the red region is the union of the blue and complement
regions. -/
theorem sdiff_red (hP : F.IsPartition) :
    Finset.univ \ F.red = F.blue ∪ F.complement := by
  ext w
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hwnotred
    have hcover : w ∈ F.red ∪ F.blue ∪ F.complement := by
      rw [hP.cover_univ]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hcover with hrb | hc
    · rcases Finset.mem_union.mp hrb with hr | hbl
      · exact absurd hr hwnotred
      · exact Or.inl hbl
    · exact Or.inr hc
  · intro hbc hr
    rcases hbc with hbl | hc
    · exact (Finset.disjoint_left.mp hP.red_disjoint_blue) hr hbl
    · exact (Finset.disjoint_left.mp hP.red_disjoint_complement) hr hc

end IsPartition

/-! ### The three-block geometry of a partitioned coarse frame

The red, blue, and complement regions of a partitioned coarse frame form a
`ThreeBlockGeometry`, unlocking the landed three-block factorization machinery of
`TNLean.PEPS.RegionBlock.UnionInjectivityGeneral` for the coarse merge collapse:
the fused complement physical leg `complPhysical`, the host vertex-product split
`prod_sdiff_red_eq_blue_mul_complement`, and the host weight as a blue/complement
double-product sum. -/

/-- **The three-block geometry of a partitioned coarse frame.** The red, blue, and
complement regions, with their pairwise disjointness and cover, packaged as a
`ThreeBlockGeometry` so the landed three-block factorizations of
`TNLean.PEPS.RegionBlock.UnionInjectivityGeneral` apply to the coarse blocking.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def toThreeBlockGeometry (hP : F.IsPartition) : ThreeBlockGeometry V where
  red := F.red
  blue := F.blue
  complement := F.complement
  red_disjoint_blue := hP.red_disjoint_blue
  red_disjoint_complement := hP.red_disjoint_complement
  blue_disjoint_complement := hP.blue_disjoint_complement
  cover_univ := hP.cover_univ

@[simp] theorem toThreeBlockGeometry_red (hP : F.IsPartition) :
    (F.toThreeBlockGeometry hP).red = F.red := rfl
@[simp] theorem toThreeBlockGeometry_blue (hP : F.IsPartition) :
    (F.toThreeBlockGeometry hP).blue = F.blue := rfl
@[simp] theorem toThreeBlockGeometry_complement (hP : F.IsPartition) :
    (F.toThreeBlockGeometry hP).complement = F.complement := rfl

/-! ### Crossing classification of region boundary edges

Under the partition, every boundary edge of a region crosses to exactly one
partner region: a boundary edge of `red` has its out-of-`red` endpoint in `blue`
or in `complement`, so it is an `r-b` or an `r-c` crossing edge. This is the
geometric content the factoring fields of a coherent frame consume: the two
super-edges incident to a super-site carry exactly the two crossing bundles of
its region's boundary. -/

/-- A vertex outside `red` lies in `blue` or in `complement`. -/
theorem mem_blue_or_complement_of_not_mem_red (hP : F.IsPartition) {w : V}
    (hw : w ∉ F.red) : w ∈ F.blue ∨ w ∈ F.complement := by
  have hbc : w ∈ F.blue ∪ F.complement := by rw [← hP.sdiff_red]; simp [hw]
  exact Finset.mem_union.mp hbc

/-- **Crossing classification at the red super-site.** A boundary edge of `red`
is an `r-b` crossing edge or an `r-c` crossing edge: its out-of-`red` endpoint
lies in `blue` or in `complement`. -/
theorem isCrossingEdge_red_blue_or_red_complement (hP : F.IsPartition) {g : Edge G}
    (hg : IsRegionBoundaryEdge (G := G) F.red g) :
    IsCrossingEdge (G := G) A F.red F.blue g ∨
      IsCrossingEdge (G := G) A F.red F.complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `g.1.1 ∈ red` (h1), `g.1.2 ∉ red` (h2): classify the out-of-red endpoint `g.1.2`.
    have h1nb : g.1.1 ∉ F.blue := (Finset.disjoint_left.mp hP.red_disjoint_blue) h1
    have h1nc : g.1.1 ∉ F.complement :=
      (Finset.disjoint_left.mp hP.red_disjoint_complement) h1
    rcases F.mem_blue_or_complement_of_not_mem_red hP h2 with hb | hc
    · exact Or.inl ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nb, hb⟩⟩
    · exact Or.inr ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nc, hc⟩⟩
  · -- `g.1.1 ∉ red` (h1), `g.1.2 ∈ red` (h2): classify the out-of-red endpoint `g.1.1`.
    have h2nb : g.1.2 ∉ F.blue := (Finset.disjoint_left.mp hP.red_disjoint_blue) h2
    have h2nc : g.1.2 ∉ F.complement :=
      (Finset.disjoint_left.mp hP.red_disjoint_complement) h2
    rcases F.mem_blue_or_complement_of_not_mem_red hP h1 with hb | hc
    · exact Or.inl ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hb, h2nb⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hc, h2nc⟩⟩

/-- **Crossing classification at the blue super-site.** A boundary edge of `blue`
is an `r-b` crossing edge or a `b-c` crossing edge. -/
theorem isCrossingEdge_red_blue_or_blue_complement (hP : F.IsPartition) {g : Edge G}
    (hg : IsRegionBoundaryEdge (G := G) F.blue g) :
    IsCrossingEdge (G := G) A F.red F.blue g ∨
      IsCrossingEdge (G := G) A F.blue F.complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `g.1.1 ∈ blue` (h1), `g.1.2 ∉ blue` (h2): classify `g.1.2` as red or complement.
    have h1nr : g.1.1 ∉ F.red := fun hr =>
      (Finset.disjoint_left.mp hP.red_disjoint_blue) hr h1
    have h1nc : g.1.1 ∉ F.complement := fun hc =>
      (Finset.disjoint_left.mp hP.blue_disjoint_complement) h1 hc
    have hbc : g.1.2 ∈ F.red ∨ g.1.2 ∈ F.complement := by
      have hcover : g.1.2 ∈ F.red ∪ F.blue ∪ F.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact Or.inl hr
        · exact absurd hbl h2
      · exact Or.inr hc
    rcases hbc with hr | hc
    · exact Or.inl ⟨Or.inr ⟨h1nr, hr⟩, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nc, hc⟩⟩
  · -- `g.1.1 ∉ blue` (h1), `g.1.2 ∈ blue` (h2): classify `g.1.1` as red or complement.
    have h2nr : g.1.2 ∉ F.red := fun hr =>
      (Finset.disjoint_left.mp hP.red_disjoint_blue) hr h2
    have h2nc : g.1.2 ∉ F.complement := fun hc =>
      (Finset.disjoint_left.mp hP.blue_disjoint_complement) h2 hc
    have hbc : g.1.1 ∈ F.red ∨ g.1.1 ∈ F.complement := by
      have hcover : g.1.1 ∈ F.red ∪ F.blue ∪ F.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact Or.inl hr
        · exact absurd hbl h1
      · exact Or.inr hc
    rcases hbc with hr | hc
    · exact Or.inl ⟨Or.inl ⟨hr, h2nr⟩, Or.inr ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hc, h2nc⟩⟩

/-- **Crossing classification at the complement super-site.** A boundary edge of
`complement` is an `r-c` crossing edge or a `b-c` crossing edge. -/
theorem isCrossingEdge_red_complement_or_blue_complement (hP : F.IsPartition)
    {g : Edge G} (hg : IsRegionBoundaryEdge (G := G) F.complement g) :
    IsCrossingEdge (G := G) A F.red F.complement g ∨
      IsCrossingEdge (G := G) A F.blue F.complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `g.1.1 ∈ complement`, `g.1.2 ∉ complement`: classify `g.1.2` as red or blue.
    have hbc : g.1.2 ∈ F.red ∨ g.1.2 ∈ F.blue := by
      have hcover : g.1.2 ∈ F.red ∪ F.blue ∪ F.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact Or.inl hr
        · exact Or.inr hbl
      · exact absurd hc h2
    -- `g.1.1 ∈ complement` (h1), so `g.1.1 ∉ red` and `g.1.1 ∉ blue`.
    have h1nr : g.1.1 ∉ F.red := fun hr =>
      (Finset.disjoint_left.mp hP.red_disjoint_complement) hr h1
    have h1nb : g.1.1 ∉ F.blue := fun hb =>
      (Finset.disjoint_left.mp hP.blue_disjoint_complement) hb h1
    rcases hbc with hr | hb
    · exact Or.inl ⟨Or.inr ⟨h1nr, hr⟩, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1nb, hb⟩, Or.inl ⟨h1, h2⟩⟩
  · -- `g.1.1 ∉ complement`, `g.1.2 ∈ complement`: classify `g.1.1` as red or blue.
    have hbc : g.1.1 ∈ F.red ∨ g.1.1 ∈ F.blue := by
      have hcover : g.1.1 ∈ F.red ∪ F.blue ∪ F.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact Or.inl hr
        · exact Or.inr hbl
      · exact absurd hc h1
    -- `g.1.2 ∈ complement` (h2), so `g.1.2 ∉ red` and `g.1.2 ∉ blue`.
    have h2nr : g.1.2 ∉ F.red := fun hr =>
      (Finset.disjoint_left.mp hP.red_disjoint_complement) hr h2
    have h2nb : g.1.2 ∉ F.blue := fun hb =>
      (Finset.disjoint_left.mp hP.blue_disjoint_complement) hb h2
    rcases hbc with hr | hb
    · exact Or.inl ⟨Or.inl ⟨hr, h2nr⟩, Or.inr ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inl ⟨hb, h2nb⟩, Or.inr ⟨h1, h2⟩⟩

end CoarseBlockingFrame

end PEPS
end TNLean
