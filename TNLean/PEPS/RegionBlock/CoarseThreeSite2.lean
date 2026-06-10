import TNLean.PEPS.RegionBlock.CoarseThreeSite

/-!
# Coherent coarse blocking frames for the normal PEPS theorem

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
incident to a super-edge agree on the shared crossing bonds
(`legEquiv_agree_on_crossing`), so the three blocked-region weights are read at a
single consistent assignment of the original crossing bonds. This is the
well-posedness layer flagged as the first remaining obligation of the coarse
three-site route in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

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

instance instFintypeCrossingConfig (A : Tensor G d) (R R' : Finset V) :
    Fintype (CrossingConfig (G := G) A R R') :=
  inferInstance

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

omit [DecidableEq V] in
@[simp] theorem edgeRegions_rb : F.edgeRegions coarseEdgeRB = (F.red, F.blue) := rfl
omit [DecidableEq V] in
@[simp] theorem edgeRegions_rc : F.edgeRegions coarseEdgeRC = (F.red, F.complement) := rfl
omit [DecidableEq V] in
@[simp] theorem edgeRegions_bc : F.edgeRegions coarseEdgeBC = (F.blue, F.complement) := rfl

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
bonds (`legEquiv_agree_on_crossing`).

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

/-! ### The shared-super-bond agreement

The factoring fields express each super-site's leg identification through the shared
bond models. Their payoff is that two super-sites incident to the same super-edge,
fed leg assignments agreeing on the shared super-bond, read every shared crossing
edge to the same original virtual leg. These are the well-posedness lemmas the state
gluing consumes: the red and blue blocked-region weights are evaluated at boundary
configurations agreeing on every red-to-blue crossing edge, and likewise for the
other two super-edges. -/

omit [DecidableEq V] in
/-- **Red and blue agree on the `r-b` crossings.** If the red and blue leg
assignments carry the same value on the shared `r-b` super-bond, the red and blue
boundary configurations they induce agree on every red-to-blue crossing edge. The
crossing edge is presented once, with its red and blue boundary memberships read off
the crossing hypothesis. -/
theorem legEquivRed_eq_legEquivBlue_on_rb
    (legsR : (ie : IncidentEdge coarseGraph 0) → Fin (F.frame.coarseBondDim ie.1))
    (legsB : (ie : IncidentEdge coarseGraph 1) → Fin (F.frame.coarseBondDim ie.1))
    (ieR : IncidentEdge coarseGraph 0) (hieR : ieR.1 = coarseEdgeRB)
    (ieB : IncidentEdge coarseGraph 1) (hieB : ieB.1 = coarseEdgeRB)
    (hval : (hieR ▸ legsR ieR : Fin (F.frame.coarseBondDim coarseEdgeRB)) = hieB ▸ legsB ieB)
    (g : Edge G) (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g) :
    (F.frame.legEquivRed legsR ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.frame.legEquivBlue legsB ⟨g, hf.2⟩ : Fin (A.bondDim g)) := by
  have hfR := F.factor_red legsR ⟨g, hf.1⟩ hf ieR hieR
  have hfB := F.factor_blue_rb legsB ⟨g, hf.2⟩ hf ieB hieB
  rw [hfR, hfB, hval]

omit [DecidableEq V] in
/-- **Red and complement agree on the `r-c` crossings.** -/
theorem legEquivRed_eq_legEquivComplement_on_rc
    (legsR : (ie : IncidentEdge coarseGraph 0) → Fin (F.frame.coarseBondDim ie.1))
    (legsC : (ie : IncidentEdge coarseGraph 2) → Fin (F.frame.coarseBondDim ie.1))
    (ieR : IncidentEdge coarseGraph 0) (hieR : ieR.1 = coarseEdgeRC)
    (ieC : IncidentEdge coarseGraph 2) (hieC : ieC.1 = coarseEdgeRC)
    (hval : (hieR ▸ legsR ieR : Fin (F.frame.coarseBondDim coarseEdgeRC)) = hieC ▸ legsC ieC)
    (g : Edge G) (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g) :
    (F.frame.legEquivRed legsR ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.frame.legEquivComplement legsC ⟨g, hf.2⟩ : Fin (A.bondDim g)) := by
  have hfR := F.factor_red_rc legsR ⟨g, hf.1⟩ hf ieR hieR
  have hfC := F.factor_compl_rc legsC ⟨g, hf.2⟩ hf ieC hieC
  rw [hfR, hfC, hval]

omit [DecidableEq V] in
/-- **Blue and complement agree on the `b-c` crossings.** -/
theorem legEquivBlue_eq_legEquivComplement_on_bc
    (legsB : (ie : IncidentEdge coarseGraph 1) → Fin (F.frame.coarseBondDim ie.1))
    (legsC : (ie : IncidentEdge coarseGraph 2) → Fin (F.frame.coarseBondDim ie.1))
    (ieB : IncidentEdge coarseGraph 1) (hieB : ieB.1 = coarseEdgeBC)
    (ieC : IncidentEdge coarseGraph 2) (hieC : ieC.1 = coarseEdgeBC)
    (hval : (hieB ▸ legsB ieB : Fin (F.frame.coarseBondDim coarseEdgeBC)) = hieC ▸ legsC ieC)
    (g : Edge G) (hf : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g) :
    (F.frame.legEquivBlue legsB ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.frame.legEquivComplement legsC ⟨g, hf.2⟩ : Fin (A.bondDim g)) := by
  have hfB := F.factor_blue_bc legsB ⟨g, hf.1⟩ hf ieB hieB
  have hfC := F.factor_compl_bc legsC ⟨g, hf.2⟩ hf ieC hieC
  rw [hfB, hfC, hval]

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
  rw [F.coarseTensor_component_red, F.coarseTensor_component_blue,
    F.coarseTensor_component_complement]

end CoarseBlockingFrame

end PEPS
end TNLean
