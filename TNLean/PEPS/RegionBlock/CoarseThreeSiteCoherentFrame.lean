/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.CoarseThreeSite
import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral

/-!
# Coherent coarse blocking frames and the three-region merge collapse

The coarse three-site tensor of `TNLean.PEPS.RegionBlock.CoarseThreeSite` records,
for each coarse super-site, an *independent* equivalence `legEquiv` between the
coarse virtual legs incident to that super-site and the region boundary
configurations. That independence is harmless for the vertex injectivity and the
coarse edge-inserted coefficient transfer, both of which read one super-site at a
time. It is, however, not enough to glue the coarse state coefficient to the
original state coefficient: each coarse super-bond is incident to **two** coarse
super-sites, so its value is read by both incident leg identifications, and the
state gluing needs those two readings to land on the **same** original crossing-bond
configuration.

## The coherent frame

This file records that missing compatibility. A `CoherentCoarseBlockingFrame`
extends a `CoarseBlockingFrame` with one bond model per coarse super-edge — an
equivalence between the coarse bond and the configurations on the original edges
crossing between the two incident regions — and requires each super-site's leg
identification to factor through these shared bond models on its incident
super-edges. The geometric content is the partition of every region's boundary
edges by the partner region across each boundary edge: a boundary edge of the red
region crosses either to the blue region or to the complement region, and the two
super-edges incident to the red super-site carry exactly those two crossing
bundles.

The coherence fields make the state gluing well posed: the two leg identifications
incident to a super-edge agree on the shared crossing bonds, since the coherence
fields (`factor_red` and `factor_blue_rb` on the red-to-blue super-edge, and their
red-to-complement and blue-to-complement siblings) route both readings through the
same bond model, so the three blocked-region weights are read at a
single consistent assignment of the original crossing bonds. This is the
well-posedness layer flagged as the first remaining obligation of the coarse
three-site route in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## The three-region merge collapse

Through those coherent bond models the closed-state coefficient of the coarse
three-site tensor is a sum over coarse virtual configurations of a product of
three original blocked-region weights
(`stateCoeff_coarseTensor_eq_threeRegionSum`). The second half of the file
collapses that triple sum to a constant times the original closed-state
coefficient, the merge collapse that glues the coarse state to the original
state.

The route fuses the blue and complement weights into the host weight over
`univ \ red` and then applies the landed two-block collapse
`stateCoeff_eq_regionComplement` of `TNLean.PEPS.RegionBlock.Recovery` for the red
region against its set complement. The constants are the interior bond products of
the three regions, all positive under positive bond dimensions.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1449--1500 of `Papers/1804.04964/paper_normal.tex`
  (the blocking) and lines 1205--1210 (the one-region-against-complement
  gluing)](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Crossing edges between two regions

An original edge crosses between two regions `R` and `R'` when it is a boundary
edge of `R` and a boundary edge of `R'`. For a partition of the vertex set into
three regions, these crossing edges are exactly the boundary edges of `R` whose
out-of-`R` endpoint lies in `R'`. The crossing configurations on these edges are
the bundle of original virtual legs carried by the coarse super-edge between the
two regions. -/

/-- An original edge crosses between the regions `R` and `R'` when it is a boundary
edge of each. For disjoint `R`, `R'` this means exactly one endpoint lies in `R`
and the other in `R'`. -/
def IsCrossingEdge (_A : Tensor G d) (R R' : Finset V) (g : Edge G) : Prop :=
  IsRegionBoundaryEdge (G := G) R g ∧ IsRegionBoundaryEdge (G := G) R' g

instance (A : Tensor G d) (R R' : Finset V) (g : Edge G) :
    Decidable (IsCrossingEdge (G := G) A R R' g) := by
  unfold IsCrossingEdge; infer_instance

omit [Fintype V] [DecidableEq V] in
/-- Crossing is symmetric in the two regions. -/
theorem IsCrossingEdge.symm {A : Tensor G d} {R R' : Finset V} {g : Edge G}
    (h : IsCrossingEdge (G := G) A R R' g) : IsCrossingEdge (G := G) A R' R g :=
  ⟨h.2, h.1⟩

omit [Fintype V] [DecidableEq V] in
/-- A crossing edge between `R` and `R'` is a boundary edge of `R`. -/
theorem IsCrossingEdge.boundary_left {A : Tensor G d} {R R' : Finset V} {g : Edge G}
    (h : IsCrossingEdge (G := G) A R R' g) : IsRegionBoundaryEdge (G := G) R g :=
  h.1

/-- The crossing configurations between `R` and `R'`: an assignment of an original
virtual leg to every edge crossing between the two regions. This is the bundle of
original bonds carried by the coarse super-edge between `R` and `R'`. -/
abbrev CrossingConfig (A : Tensor G d) (R R' : Finset V) : Type _ :=
  (g : {g : Edge G // IsCrossingEdge (G := G) A R R' g}) → Fin (A.bondDim g.1)

/-! ### The partner region of a coarse super-edge

The coarse super-edge `r-b` (`coarseEdgeRB`) bundles the red-to-blue crossings,
`r-c` (`coarseEdgeRC`) the red-to-complement crossings, and `b-c` (`coarseEdgeBC`)
the blue-to-complement crossings. For a coarse super-site `v` and an incident
super-edge `f`, the partner region is the region attached to the other endpoint of
`f`. -/

namespace CoarseBlockingFrame

variable {A : Tensor G d} (F : CoarseBlockingFrame (G := G) (d := d) A)

/-- The two endpoints of a coarse super-edge, as the regions they attach. The coarse
graph is the complete graph on `Fin 3`, so the endpoints of an edge are its two
coordinate entries. -/
def edgeRegions (f : Edge coarseGraph) : Finset V × Finset V :=
  (F.regionOf f.1.1, F.regionOf f.1.2)

end CoarseBlockingFrame

/-! ### The coherent coarse blocking frame

A coherent frame fixes, for each coarse super-edge `f`, an equivalence between the
coarse bond `Fin (coarseBondDim f)` and the crossing configurations between the two
regions attached to the endpoints of `f`. The factoring fields then require each
super-site's leg identification to read each incident super-bond through the shared
bond model on the corresponding crossing edges. -/

/-- **A coherent coarse blocking frame.** A coarse blocking frame together with, for
each coarse super-edge, a bond model identifying the coarse bond with the original
crossing configurations between the two incident regions, and the requirement that
each super-site's leg identification factors through these shared bond models on its
incident super-edges.

The factoring fields `factor_red`, `factor_blue`, `factor_complement` say: reading a
boundary edge `g` of the region at super-site `v`, where `g` crosses to the partner
region across an incident super-edge `f`, the region boundary configuration assigned
by `legEquiv v legs` equals the bond model of `f` applied to the coarse leg
`legs ⟨f, _⟩` read at `g`. Two super-sites incident to `f` therefore read the shared
super-bond value through the *same* bond model, so they agree on the shared crossing
bonds (`factor_red` against `factor_blue_rb` on the red-to-blue super-edge, and
likewise for the red-to-complement and blue-to-complement pairs).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 and
1205--1210 of `Papers/1804.04964/paper_normal.tex`. -/
structure CoherentCoarseBlockingFrame (A : Tensor G d)
    extends CoarseBlockingFrame (G := G) (d := d) A where
  /-- For each coarse super-edge, an equivalence between the coarse bond and the
  original crossing configurations between the two incident regions. -/
  bondModel : (f : Edge coarseGraph) →
    Fin (toCoarseBlockingFrame.coarseBondDim f) ≃
      CrossingConfig (G := G) A (toCoarseBlockingFrame.edgeRegions f).1
        (toCoarseBlockingFrame.edgeRegions f).2
  /-- The red super-site reads each boundary edge of the red region through the bond
  model of the incident super-edge whose partner region contains the out-of-red
  endpoint. The two incident super-edges of the red super-site are `r-b` and `r-c`. -/
  factor_red :
    ∀ (legs : (ie : IncidentEdge coarseGraph 0) →
        Fin (toCoarseBlockingFrame.coarseBondDim ie.1))
      (b : {b : Edge G // IsRegionBoundaryEdge (G := G) toCoarseBlockingFrame.red b})
      (hf : IsCrossingEdge (G := G) A toCoarseBlockingFrame.red toCoarseBlockingFrame.blue b.1)
      (ie : IncidentEdge coarseGraph 0) (hie : ie.1 = coarseEdgeRB),
      toCoarseBlockingFrame.legEquivRed legs b =
        (bondModel coarseEdgeRB (hie ▸ legs ie)
          ⟨b.1, hf⟩ :
          Fin (A.bondDim b.1))
  /-- The factoring of the red super-site at the `r-c` super-edge. -/
  factor_red_rc :
    ∀ (legs : (ie : IncidentEdge coarseGraph 0) →
        Fin (toCoarseBlockingFrame.coarseBondDim ie.1))
      (b : {b : Edge G // IsRegionBoundaryEdge (G := G) toCoarseBlockingFrame.red b})
      (hf : IsCrossingEdge (G := G) A toCoarseBlockingFrame.red
        toCoarseBlockingFrame.complement b.1)
      (ie : IncidentEdge coarseGraph 0) (hie : ie.1 = coarseEdgeRC),
      toCoarseBlockingFrame.legEquivRed legs b =
        (bondModel coarseEdgeRC (hie ▸ legs ie)
          ⟨b.1, hf⟩ :
          Fin (A.bondDim b.1))
  /-- The blue super-site reads each boundary edge of the blue region crossing to red
  through the `r-b` bond model. -/
  factor_blue_rb :
    ∀ (legs : (ie : IncidentEdge coarseGraph 1) →
        Fin (toCoarseBlockingFrame.coarseBondDim ie.1))
      (b : {b : Edge G // IsRegionBoundaryEdge (G := G) toCoarseBlockingFrame.blue b})
      (hf : IsCrossingEdge (G := G) A toCoarseBlockingFrame.red toCoarseBlockingFrame.blue b.1)
      (ie : IncidentEdge coarseGraph 1) (hie : ie.1 = coarseEdgeRB),
      toCoarseBlockingFrame.legEquivBlue legs b =
        (bondModel coarseEdgeRB (hie ▸ legs ie)
          ⟨b.1, hf⟩ :
          Fin (A.bondDim b.1))
  /-- The blue super-site reads each boundary edge of the blue region crossing to the
  complement through the `b-c` bond model. -/
  factor_blue_bc :
    ∀ (legs : (ie : IncidentEdge coarseGraph 1) →
        Fin (toCoarseBlockingFrame.coarseBondDim ie.1))
      (b : {b : Edge G // IsRegionBoundaryEdge (G := G) toCoarseBlockingFrame.blue b})
      (hf : IsCrossingEdge (G := G) A toCoarseBlockingFrame.blue
        toCoarseBlockingFrame.complement b.1)
      (ie : IncidentEdge coarseGraph 1) (hie : ie.1 = coarseEdgeBC),
      toCoarseBlockingFrame.legEquivBlue legs b =
        (bondModel coarseEdgeBC (hie ▸ legs ie)
          ⟨b.1, hf⟩ :
          Fin (A.bondDim b.1))
  /-- The complement super-site reads each boundary edge of the complement crossing to
  red through the `r-c` bond model (with the regions swapped). -/
  factor_compl_rc :
    ∀ (legs : (ie : IncidentEdge coarseGraph 2) →
        Fin (toCoarseBlockingFrame.coarseBondDim ie.1))
      (b : {b : Edge G //
        IsRegionBoundaryEdge (G := G) toCoarseBlockingFrame.complement b})
      (hf : IsCrossingEdge (G := G) A toCoarseBlockingFrame.red
        toCoarseBlockingFrame.complement b.1)
      (ie : IncidentEdge coarseGraph 2) (hie : ie.1 = coarseEdgeRC),
      toCoarseBlockingFrame.legEquivComplement legs b =
        (bondModel coarseEdgeRC (hie ▸ legs ie)
          ⟨b.1, hf⟩ :
          Fin (A.bondDim b.1))
  /-- The complement super-site reads each boundary edge of the complement crossing to
  blue through the `b-c` bond model (with the regions swapped). -/
  factor_compl_bc :
    ∀ (legs : (ie : IncidentEdge coarseGraph 2) →
        Fin (toCoarseBlockingFrame.coarseBondDim ie.1))
      (b : {b : Edge G //
        IsRegionBoundaryEdge (G := G) toCoarseBlockingFrame.complement b})
      (hf : IsCrossingEdge (G := G) A toCoarseBlockingFrame.blue
        toCoarseBlockingFrame.complement b.1)
      (ie : IncidentEdge coarseGraph 2) (hie : ie.1 = coarseEdgeBC),
      toCoarseBlockingFrame.legEquivComplement legs b =
        (bondModel coarseEdgeBC (hie ▸ legs ie)
          ⟨b.1, hf⟩ :
          Fin (A.bondDim b.1))

namespace CoherentCoarseBlockingFrame

variable {A : Tensor G d} (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)

/-- The underlying coarse blocking frame. -/
abbrev frame : CoarseBlockingFrame (G := G) (d := d) A := F.toCoarseBlockingFrame

end CoherentCoarseBlockingFrame

/-! ### The coarse state coefficient as a product of three region weights

The coarse tensor lives on the three-vertex complete graph, so its closed-state
coefficient is a sum over the three coarse super-bonds of the product over the three
coarse super-sites of the coarse components. Each coarse super-site component is, by
construction, a single original blocked-region weight read at the leg-identified
boundary configuration. The reductions below rewrite the coarse closed-state
coefficient as the explicit sum over coarse virtual configurations of the product of
the red, blue, and complement original blocked-region weights. This is the entry
point of the state gluing: what remains is the three-region merge collapse refactoring
this sum, through the coherent bond models, as a constant times the original closed
state coefficient. -/

namespace CoarseBlockingFrame

variable {A : Tensor G d} (F : CoarseBlockingFrame (G := G) (d := d) A)

/-- The coarse red super-site component is the original red blocked-region weight. -/
theorem coarseTensor_component_red
    (legs : (ie : IncidentEdge coarseGraph 0) → Fin (F.coarseBondDim ie.1))
    (p : Fin (coarseDim V d)) :
    (F.coarseTensor).component 0 legs p =
      regionBlockedWeight (G := G) A F.red (F.legEquivRed legs) (coarseProj F.red p) := by
  rw [F.coarseTensor_component]; rfl

/-- The coarse blue super-site component is the original blue blocked-region weight. -/
theorem coarseTensor_component_blue
    (legs : (ie : IncidentEdge coarseGraph 1) → Fin (F.coarseBondDim ie.1))
    (p : Fin (coarseDim V d)) :
    (F.coarseTensor).component 1 legs p =
      regionBlockedWeight (G := G) A F.blue (F.legEquivBlue legs) (coarseProj F.blue p) := by
  rw [F.coarseTensor_component]; rfl

/-- The coarse complement super-site component is the original complement
blocked-region weight. -/
theorem coarseTensor_component_complement
    (legs : (ie : IncidentEdge coarseGraph 2) → Fin (F.coarseBondDim ie.1))
    (p : Fin (coarseDim V d)) :
    (F.coarseTensor).component 2 legs p =
      regionBlockedWeight (G := G) A F.complement (F.legEquivComplement legs)
        (coarseProj F.complement p) := by
  rw [F.coarseTensor_component]; rfl

/-- **The coarse state coefficient as a sum of three-region weight products.** The
closed-state coefficient of the coarse tensor is the sum over coarse virtual
configurations of the product of the red, blue, and complement original
blocked-region weights, each read at the boundary configuration its leg
identification assigns from the coarse virtual configuration.

This is the three-region form of the coarse closed state, the entry point of the
state gluing. The remaining content is the merge collapse to a constant times the
original closed state coefficient, documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`. -/
theorem stateCoeff_coarseTensor_eq_threeRegionSum (s : Fin 3 → Fin (coarseDim V d)) :
    stateCoeff (F.coarseTensor) s =
      ∑ η : VirtualConfig (F.coarseTensor),
        regionBlockedWeight (G := G) A F.red
            (F.legEquivRed (fun ie => η ie.1)) (coarseProj F.red (s 0)) *
          regionBlockedWeight (G := G) A F.blue
            (F.legEquivBlue (fun ie => η ie.1)) (coarseProj F.blue (s 1)) *
          regionBlockedWeight (G := G) A F.complement
            (F.legEquivComplement (fun ie => η ie.1)) (coarseProj F.complement (s 2)) := by
  rw [stateCoeff]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  rw [Fin.prod_univ_three]
  let legsRed : (ie : IncidentEdge coarseGraph 0) → Fin (F.coarseBondDim ie.1) :=
    fun ie => η ie.1
  let legsBlue : (ie : IncidentEdge coarseGraph 1) → Fin (F.coarseBondDim ie.1) :=
    fun ie => η ie.1
  let legsComplement : (ie : IncidentEdge coarseGraph 2) → Fin (F.coarseBondDim ie.1) :=
    fun ie => η ie.1
  change F.coarseTensor.component 0 legsRed (s 0) *
      F.coarseTensor.component 1 legsBlue (s 1) *
      F.coarseTensor.component 2 legsComplement (s 2) = _
  rw [F.coarseTensor_component_red, F.coarseTensor_component_blue,
    F.coarseTensor_component_complement]

end CoarseBlockingFrame

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
the fused complement physical leg `ThreeBlockGeometry.complPhysical`, the host
vertex-product split `ThreeBlockGeometry.prod_sdiff_red_eq_blue_mul_complement`,
and the host weight as a blue/complement double-product sum. -/

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

/-! ### Incident super-edges of the coarse graph

Each coarse super-site has two incident super-edges. The red super-site `0` is
incident to `r-b` and `r-c`, the blue super-site `1` to `r-b` and `b-c`, the
complement super-site `2` to `r-c` and `b-c`. These named incident edges feed the
factoring fields of a coherent frame, which read a super-bond off the coarse leg
at the corresponding incident edge. -/

/-- The incident super-edge `r-b` at the red super-site `0`. -/
def incidentRB0 : IncidentEdge coarseGraph 0 := ⟨coarseEdgeRB, Or.inl rfl⟩

/-- The incident super-edge `r-c` at the red super-site `0`. -/
def incidentRC0 : IncidentEdge coarseGraph 0 := ⟨coarseEdgeRC, Or.inl rfl⟩

/-- The incident super-edge `r-b` at the blue super-site `1`. -/
def incidentRB1 : IncidentEdge coarseGraph 1 := ⟨coarseEdgeRB, Or.inr rfl⟩

/-- The incident super-edge `b-c` at the blue super-site `1`. -/
def incidentBC1 : IncidentEdge coarseGraph 1 := ⟨coarseEdgeBC, Or.inl rfl⟩

/-- The incident super-edge `r-c` at the complement super-site `2`. -/
def incidentRC2 : IncidentEdge coarseGraph 2 := ⟨coarseEdgeRC, Or.inr rfl⟩

/-- The incident super-edge `b-c` at the complement super-site `2`. -/
def incidentBC2 : IncidentEdge coarseGraph 2 := ⟨coarseEdgeBC, Or.inr rfl⟩

/-! ### Reading a region boundary leg off the bond models

Through the factoring fields, each super-site's leg identification of a coarse
virtual configuration `η` reads every boundary edge of its region off one of the
two bond models on its incident super-edges. The crossing classification selects
which model: a boundary edge of `red` crossing to `blue` is read off the `r-b`
bond model at `η`'s `r-b` value, a boundary edge crossing to `complement` off the
`r-c` bond model at `η`'s `r-c` value. These read-offs are the per-edge form of
the shared-super-bond agreement; they will express each coarse blocked-region
weight as a function of the original crossing configurations alone. -/

namespace CoherentCoarseBlockingFrame

variable {A : Tensor G d} (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)

/-- **Red leg off the `r-b` bond model.** On a red boundary edge crossing to blue,
the red super-site reads the leg of a coarse virtual configuration `η` off the
`r-b` bond model at `η`'s `r-b` value. -/
theorem legEquivRed_eq_bondModel_rb
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g) :
    (F.frame.legEquivRed (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeRB (η coarseEdgeRB) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_red (fun ie => η ie.1) ⟨g, hf.1⟩ hf incidentRB0 rfl

/-- **Red leg off the `r-c` bond model.** On a red boundary edge crossing to the
complement, the red super-site reads the leg of `η` off the `r-c` bond model at
`η`'s `r-c` value. -/
theorem legEquivRed_eq_bondModel_rc
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g) :
    (F.frame.legEquivRed (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeRC (η coarseEdgeRC) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_red_rc (fun ie => η ie.1) ⟨g, hf.1⟩ hf incidentRC0 rfl

/-- **Blue leg off the `r-b` bond model.** On a blue boundary edge crossing to red,
the blue super-site reads the leg of `η` off the `r-b` bond model. -/
theorem legEquivBlue_eq_bondModel_rb
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g) :
    (F.frame.legEquivBlue (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeRB (η coarseEdgeRB) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_blue_rb (fun ie => η ie.1) ⟨g, hf.2⟩ hf incidentRB1 rfl

/-- **Blue leg off the `b-c` bond model.** On a blue boundary edge crossing to the
complement, the blue super-site reads the leg of `η` off the `b-c` bond model. -/
theorem legEquivBlue_eq_bondModel_bc
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g) :
    (F.frame.legEquivBlue (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeBC (η coarseEdgeBC) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_blue_bc (fun ie => η ie.1) ⟨g, hf.1⟩ hf incidentBC1 rfl

/-- **Complement leg off the `r-c` bond model.** On a complement boundary edge
crossing to red, the complement super-site reads the leg of `η` off the `r-c`
bond model. -/
theorem legEquivComplement_eq_bondModel_rc
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g) :
    (F.frame.legEquivComplement (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeRC (η coarseEdgeRC) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_compl_rc (fun ie => η ie.1) ⟨g, hf.2⟩ hf incidentRC2 rfl

/-- **Complement leg off the `b-c` bond model.** On a complement boundary edge
crossing to blue, the complement super-site reads the leg of `η` off the `b-c`
bond model. -/
theorem legEquivComplement_eq_bondModel_bc
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g) :
    (F.frame.legEquivComplement (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeBC (η coarseEdgeBC) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_compl_bc (fun ie => η ie.1) ⟨g, hf.2⟩ hf incidentBC2 rfl

/-! ### The region boundary configs as functions of the crossing configs

Assembling the per-edge read-offs with the crossing classification, each coarse
region weight's boundary configuration is a function of the three original
crossing configurations alone. The red boundary configuration reads each red
boundary edge off the `r-b` bond model (if it crosses to blue) or the `r-c` bond
model (if it crosses to complement); the classification is a genuine dichotomy
because blue and complement are disjoint. This expresses `legEquivRed (fun ie =>
η ie.1)` entirely through `bondModel rb (η rb)` and `bondModel rc (η rc)`, the
form the merge collapse contracts against the original crossing edges. -/

open scoped Classical in
/-- The red boundary configuration induced by a coarse virtual configuration `η`
is determined by the `r-b` and `r-c` bond models at `η`'s values: on a red
boundary edge crossing to blue it reads the `r-b` model, on one crossing to the
complement it reads the `r-c` model. Under the partition every red boundary edge
crosses to exactly one of blue or complement. -/
theorem legEquivRed_apply_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G) F.frame.red b}) :
    (F.frame.legEquivRed (fun ie => η ie.1) b : Fin (A.bondDim b.1)) =
      if hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1 then
        (F.bondModel coarseEdgeRB (η coarseEdgeRB) ⟨b.1, hb⟩ : Fin (A.bondDim b.1))
      else
        (F.bondModel coarseEdgeRC (η coarseEdgeRC)
          ⟨b.1, (F.frame.isCrossingEdge_red_blue_or_red_complement hP b.2).resolve_left hb⟩ :
          Fin (A.bondDim b.1)) := by
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1
  · rw [dite_eq_left hb]
    have := F.legEquivRed_eq_bondModel_rb η b.1 hb
    -- `⟨b.1, hb.1⟩ = b` as subtype elements (same edge, proof-irrelevant membership).
    simpa using this
  · rw [dite_eq_right hb]
    have hc : IsCrossingEdge (G := G) A F.frame.red F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_blue_or_red_complement hP b.2).resolve_left hb
    have := F.legEquivRed_eq_bondModel_rc η b.1 hc
    simpa using this

open scoped Classical in
/-- The blue boundary configuration induced by `η`: on a blue boundary edge
crossing to red it reads the `r-b` bond model, on one crossing to the complement
it reads the `b-c` bond model. -/
theorem legEquivBlue_apply_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G) F.frame.blue b}) :
    (F.frame.legEquivBlue (fun ie => η ie.1) b : Fin (A.bondDim b.1)) =
      if hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1 then
        (F.bondModel coarseEdgeRB (η coarseEdgeRB) ⟨b.1, hb⟩ : Fin (A.bondDim b.1))
      else
        (F.bondModel coarseEdgeBC (η coarseEdgeBC)
          ⟨b.1, (F.frame.isCrossingEdge_red_blue_or_blue_complement hP b.2).resolve_left hb⟩ :
          Fin (A.bondDim b.1)) := by
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1
  · rw [dite_eq_left hb]
    have := F.legEquivBlue_eq_bondModel_rb η b.1 hb
    simpa using this
  · rw [dite_eq_right hb]
    have hc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_blue_or_blue_complement hP b.2).resolve_left hb
    have := F.legEquivBlue_eq_bondModel_bc η b.1 hc
    simpa using this

open scoped Classical in
/-- The complement boundary configuration induced by `η`: on a complement
boundary edge crossing to red it reads the `r-c` bond model, on one crossing to
blue it reads the `b-c` bond model. -/
theorem legEquivComplement_apply_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G) F.frame.complement b}) :
    (F.frame.legEquivComplement (fun ie => η ie.1) b : Fin (A.bondDim b.1)) =
      if hb : IsCrossingEdge (G := G) A F.frame.red F.frame.complement b.1 then
        (F.bondModel coarseEdgeRC (η coarseEdgeRC) ⟨b.1, hb⟩ : Fin (A.bondDim b.1))
      else
        (F.bondModel coarseEdgeBC (η coarseEdgeBC)
          ⟨b.1, (F.frame.isCrossingEdge_red_complement_or_blue_complement hP
            b.2).resolve_left hb⟩ :
          Fin (A.bondDim b.1)) := by
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.complement b.1
  · rw [dite_eq_left hb]
    have := F.legEquivComplement_eq_bondModel_rc η b.1 hb
    simpa using this
  · rw [dite_eq_right hb]
    have hc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_complement_or_blue_complement hP b.2).resolve_left hb
    have := F.legEquivComplement_eq_bondModel_bc η b.1 hc
    simpa using this

end CoherentCoarseBlockingFrame

end PEPS
end TNLean
