import TNLean.PEPS.RegionTransport
import TNLean.PEPS.NormalEdgeBlockingData
import TNLean.PEPS.RegionBlock.CoarseThreeSite2
import TNLean.PEPS.RegionBlock.UnionClosure

/-!
# Transport of one-edge blocking data along a graph isomorphism

A one-edge blocking datum over `regionInjectivityDataOf A` at an edge `e` transports along a
graph isomorphism `φ : G ≃g G'` to a one-edge blocking datum over
`regionInjectivityDataOf (A.transport φ)` at the image edge `Edge.map φ e`.  Its three blocks
are the image regions of the original blocks, blocked-tensor injective by
`regionBlockedTensorInjective_transport`, partitioning the vertex set because images of a
partition partition.  The endpoint memberships are read off the image-edge endpoints; the edge
action may swap the lexicographic order of the two endpoints, so the red and blue blocks are
exchanged exactly when the order flips, leaving the unordered datum intact
(`transportBlockingDataAlong`).

The red-to-blue crossing transports because crossing is the conjunction of two boundary-edge
conditions, each preserved by `isRegionBoundaryEdge_map`
(`isCrossingEdge_transportBlockingDataAlong`).

This is the mechanism that carries one reference blocking datum on the discrete torus to every
translate of the reference edge: a translation-invariant tensor satisfies
`A.transport (translate a b) = A`, so the transported datum is a datum for the *same* tensor at
the translated edge.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1407--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V W : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  [Fintype W] [DecidableEq W] [LinearOrder W]
  {G : SimpleGraph V} {G' : SimpleGraph W} {d : ℕ}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-! ### Image-partition bookkeeping -/

omit [Fintype V] [DecidableEq V] [LinearOrder V] [Fintype W] [DecidableEq W] [LinearOrder W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- The image of a partition under `φ` partitions the image: disjoint image regions stay
disjoint, and the union of images covers the vertex set when the originals do. -/
theorem Region_map_disjoint (φ : G ≃g G') {R S : Finset V} (h : Disjoint R S) :
    Disjoint (Region.map φ R) (Region.map φ S) := by
  rw [Finset.disjoint_left]
  intro w hwR hwS
  rw [mem_Region_map] at hwR hwS
  exact Finset.disjoint_left.mp h hwR hwS

omit [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- The image of a union is the union of images. -/
theorem Region_map_union (φ : G ≃g G') (R S : Finset V) :
    Region.map φ (R ∪ S) = Region.map φ R ∪ Region.map φ S := by
  ext w; simp only [mem_Region_map, Finset.mem_union]

omit [DecidableEq V] [LinearOrder V] [DecidableEq W] [LinearOrder W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- The image of the full vertex set is the full vertex set. -/
theorem Region_map_univ (φ : G ≃g G') :
    Region.map φ (Finset.univ : Finset V) = (Finset.univ : Finset W) := by
  ext w; simp only [mem_Region_map, Finset.mem_univ]

/-! ### The image block is injective for the transported tensor -/

omit [DecidableEq V] [DecidableEq W] in
/-- The image of a blocked-tensor-injective region for `A` is blocked-tensor injective for
`A.transport φ`. -/
theorem regionInjectivityDataOf_transport_map (A : Tensor G d) (φ : G ≃g G') {R : Finset V}
    (hR : (regionInjectivityDataOf (G := G) A).IsInjective R) :
    (regionInjectivityDataOf (G := G') (A.transport φ)).IsInjective (Region.map φ R) := by
  rw [regionInjectivityDataOf_isInjective] at hR ⊢
  exact (regionBlockedTensorInjective_transport A φ R).mpr hR

/-! ### Transport of a one-edge blocking datum

The edge action `Edge.map φ` may swap the lexicographic order of the two endpoints.  The
endpoint memberships of `NormalEdgeBlockingData` require the first endpoint of the image edge
in the red block and the second in the blue block, so the red and blue blocks are exchanged
exactly when the order flips.  Both orientations are handled by reading off `Edge.map_endpoints`.
The crossing edge is symmetric in red and blue, so the single-crossing hypothesis transports
either way. -/

open scoped Classical in
/-- **Transport of a one-edge blocking datum along a graph isomorphism.**

A one-edge blocking datum over `regionInjectivityDataOf A` at `e` gives a one-edge blocking
datum over `regionInjectivityDataOf (A.transport φ)` at `Edge.map φ e`.  The blocks are the
image regions; red and blue are exchanged when the edge action flips the endpoint order, so the
first image-edge endpoint lands in the (possibly exchanged) red block.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def transportBlockingDataAlong (A : Tensor G d) (φ : G ≃g G') {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    NormalEdgeBlockingData (regionInjectivityDataOf (G := G') (A.transport φ)) G'
      (Edge.map φ e) :=
  if hord : (Edge.map φ e).1.1 = φ e.1.1 then
    { red := Region.map φ D.red
      blue := Region.map φ D.blue
      complement := Region.map φ D.complement
      left_mem_red := by
        rw [hord]; exact (mem_Region_map_apply φ D.red e.1.1).mpr D.left_mem_red
      right_mem_blue := by
        have h2 : (Edge.map φ e).1.2 = φ e.1.2 :=
          (Edge.map_endpoints φ e).resolve_right (fun h => by
            rw [h.1] at hord; exact (G.ne_of_adj e.2.2) (φ.injective hord).symm) |>.2
        rw [h2]; exact (mem_Region_map_apply φ D.blue e.1.2).mpr D.right_mem_blue
      red_injective := regionInjectivityDataOf_transport_map A φ D.red_injective
      blue_injective := regionInjectivityDataOf_transport_map A φ D.blue_injective
      complement_injective := regionInjectivityDataOf_transport_map A φ D.complement_injective
      red_disjoint_blue := Region_map_disjoint φ D.red_disjoint_blue
      red_disjoint_complement := Region_map_disjoint φ D.red_disjoint_complement
      blue_disjoint_complement := Region_map_disjoint φ D.blue_disjoint_complement
      cover_univ := by
        rw [← Region_map_union, ← Region_map_union, D.cover_univ, Region_map_univ] }
  else
    { red := Region.map φ D.blue
      blue := Region.map φ D.red
      complement := Region.map φ D.complement
      left_mem_red := by
        have h1 : (Edge.map φ e).1.1 = φ e.1.2 :=
          (Edge.map_endpoints φ e).resolve_left (fun h => hord h.1) |>.1
        rw [h1]; exact (mem_Region_map_apply φ D.blue e.1.2).mpr D.right_mem_blue
      right_mem_blue := by
        have h2 : (Edge.map φ e).1.2 = φ e.1.1 :=
          (Edge.map_endpoints φ e).resolve_left (fun h => hord h.1) |>.2
        rw [h2]; exact (mem_Region_map_apply φ D.red e.1.1).mpr D.left_mem_red
      red_injective := regionInjectivityDataOf_transport_map A φ D.blue_injective
      blue_injective := regionInjectivityDataOf_transport_map A φ D.red_injective
      complement_injective := regionInjectivityDataOf_transport_map A φ D.complement_injective
      red_disjoint_blue := (Region_map_disjoint φ D.red_disjoint_blue).symm
      red_disjoint_complement := Region_map_disjoint φ D.blue_disjoint_complement
      blue_disjoint_complement := Region_map_disjoint φ D.red_disjoint_complement
      cover_univ := by
        rw [← Region_map_union, ← Region_map_union, Finset.union_comm D.blue D.red,
          D.cover_univ, Region_map_univ] }

/-! ### Crossing-edge transport

An edge crosses between two image regions iff its preimage crosses between the original
regions.  Crossing is the conjunction of two boundary-edge conditions, each carried across by
`isRegionBoundaryEdge_map`. -/

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
/-- The crossing edges between two image regions are the images of the crossing edges between
the originals: `Edge.map φ g'` crosses between the image regions iff `g'` crosses between the
originals. -/
theorem isCrossingEdge_Region_map (A : Tensor G d) (φ : G ≃g G') (R R' : Finset V)
    (g' : Edge G) :
    IsCrossingEdge (G := G') (A.transport φ) (Region.map φ R) (Region.map φ R')
        (Edge.map φ g') ↔
      IsCrossingEdge (G := G) A R R' g' := by
  rw [IsCrossingEdge, IsCrossingEdge, isRegionBoundaryEdge_map, isRegionBoundaryEdge_map]

/-- The transported datum's red and blue blocks are the image red and blue blocks, in some
order: in either branch the unordered pair `{red, blue}` is the image of the original pair.
This is the statement that lets the single-crossing hypothesis transport regardless of the
endpoint-order flip. -/
theorem transportBlockingDataAlong_redBlue (A : Tensor G d) (φ : G ≃g G') {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    ((transportBlockingDataAlong A φ D).red = Region.map φ D.red ∧
        (transportBlockingDataAlong A φ D).blue = Region.map φ D.blue) ∨
      ((transportBlockingDataAlong A φ D).red = Region.map φ D.blue ∧
        (transportBlockingDataAlong A φ D).blue = Region.map φ D.red) := by
  classical
  unfold transportBlockingDataAlong
  by_cases hord : (Edge.map φ e).1.1 = φ e.1.1
  · rw [dif_pos hord]; exact Or.inl ⟨rfl, rfl⟩
  · rw [dif_neg hord]; exact Or.inr ⟨rfl, rfl⟩

/-- The transported datum's complement block is the image of the original complement block, on
both endpoint-order branches.  The endpoint-order flip exchanges only the red and blue blocks; the
complement is untouched.  This is the half of the unordered-pair identity that the covariance
chain reads off directly, since the region-inserted coefficient over the complement-side block is
the same on both branches. -/
theorem transportBlockingDataAlong_complement (A : Tensor G d) (φ : G ≃g G') {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    (transportBlockingDataAlong A φ D).complement = Region.map φ D.complement := by
  classical
  unfold transportBlockingDataAlong
  by_cases hord : (Edge.map φ e).1.1 = φ e.1.1
  · rw [dif_pos hord]
  · rw [dif_neg hord]

/-- **Orientation-free red/blue host injectivity of the transported datum.**

On both endpoint-order branches the transported datum's set-complement host region of its red
block `univ \ (transportBlockingDataAlong A φ D).red` is one of the two image host regions
`univ \ Region.map φ D.red` or `univ \ Region.map φ D.blue`, both injective for `A.transport φ`.
Since the per-edge gauge of the transported datum reads the region-inserted coefficient over its
red block against this host, the host injectivity is available on both branches: the endpoint-order
flip exchanges which of the two injective image blocks plays the red role, but both are injective,
so the gauge interface input is unconditional.  This is what lets the class-agreement chain be
stated without case-splitting on the branch. -/
theorem regionBlockedTensorInjective_transportBlockingDataAlong_red (A : Tensor G d) (φ : G ≃g G')
    {e : Edge G} (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    (regionInjectivityDataOf (G := G') (A.transport φ)).IsInjective
      (transportBlockingDataAlong A φ D).red := by
  classical
  rcases transportBlockingDataAlong_redBlue A φ D with ⟨hr, _⟩ | ⟨hr, _⟩
  · rw [hr]; exact regionInjectivityDataOf_transport_map A φ D.red_injective
  · rw [hr]; exact regionInjectivityDataOf_transport_map A φ D.blue_injective

/-- **Orientation-free host injectivity of the transported datum.**

On both endpoint-order branches the set complement of the transported datum's red block is the
union of the other two image blocks, both injective for `A.transport φ`, so under union closure the
host region `univ \ (transportBlockingDataAlong A φ D).red` is itself injective.  This is the second
host injectivity the gauge interface consumes (alongside the red injectivity
`regionBlockedTensorInjective_transportBlockingDataAlong_red`), available unconditionally on the
branch: whichever image block plays the red role, the remaining two cover the host and are both
injective.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_host_transportBlockingDataAlong (A : Tensor G d) (φ : G ≃g G')
    {e : Edge G} (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hU : RegionInjectivityUnionClosure (regionInjectivityDataOf (G := G') (A.transport φ))) :
    (regionInjectivityDataOf (G := G') (A.transport φ)).IsInjective
      (Finset.univ \ (transportBlockingDataAlong A φ D).red) := by
  classical
  set D' := transportBlockingDataAlong A φ D with hD'
  -- The host region of the red block is the union of the blue and complement blocks.
  have hsdiff : Finset.univ \ D'.red = D'.blue ∪ D'.complement := by
    have hcov := D'.cover_univ
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro _
      have hmem : v ∈ D'.red ∪ D'.blue ∪ D'.complement := by rw [hcov]; exact Finset.mem_univ v
      simp only [Finset.mem_union] at hmem
      tauto
    · rintro (hb | hc)
      · exact fun hr => Finset.disjoint_left.mp D'.red_disjoint_blue hr hb
      · exact fun hr => Finset.disjoint_left.mp D'.red_disjoint_complement hr hc
  rw [hsdiff]
  exact hU.union_injective D'.blue_injective D'.complement_injective

/-- **Single-crossing transport.**

If the red-to-blue crossings of `D` are exactly the edge `e`, then the red-to-blue crossings of
the transported datum are exactly the image edge `Edge.map φ e`.  Crossing is symmetric in the
two blocks, so the endpoint-order flip that may exchange the transported red and blue blocks
does not change the crossing edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_transportBlockingDataAlong (A : Tensor G d) (φ : G ≃g G') {e : Edge G}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hsingle : ∀ g : Edge G,
      IsCrossingEdge (G := G) A D.red D.blue g ↔ g = e)
    (g : Edge G') :
    IsCrossingEdge (G := G') (A.transport φ) (transportBlockingDataAlong A φ D).red
        (transportBlockingDataAlong A φ D).blue g ↔
      g = Edge.map φ e := by
  -- Reduce the crossing condition to a crossing between the image red and image blue blocks.
  have hcross : IsCrossingEdge (G := G') (A.transport φ)
      (transportBlockingDataAlong A φ D).red (transportBlockingDataAlong A φ D).blue g ↔
        IsCrossingEdge (G := G') (A.transport φ) (Region.map φ D.red) (Region.map φ D.blue) g := by
    rcases transportBlockingDataAlong_redBlue A φ D with ⟨hr, hb⟩ | ⟨hr, hb⟩
    · rw [hr, hb]
    · rw [hr, hb]; exact ⟨IsCrossingEdge.symm, IsCrossingEdge.symm⟩
  rw [hcross]
  -- Carry the crossing back to the original tensor along the inverse edge action.
  have hback : IsCrossingEdge (G := G') (A.transport φ) (Region.map φ D.red)
      (Region.map φ D.blue) g ↔ IsCrossingEdge (G := G) A D.red D.blue (Edge.map φ.symm g) := by
    rw [← isCrossingEdge_Region_map A φ D.red D.blue (Edge.map φ.symm g), Edge.map_map_symm]
  rw [hback, hsingle]
  -- `Edge.map φ.symm g = e ↔ g = Edge.map φ e` by the edge bijection.
  constructor
  · intro h; rw [← h, Edge.map_map_symm]
  · intro h; rw [h, Edge.map_symm_map]

end PEPS
end TNLean
