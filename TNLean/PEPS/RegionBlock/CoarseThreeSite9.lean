import TNLean.PEPS.RegionBlock.CoarseThreeSite8

/-!
# The relaxed-triple merge collapse for the normal PEPS theorem

The relaxed-triple reindexing `TNLean.PEPS.mCoupledThreeRegionSum_eq_relaxedTripleSum` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite7` writes the coarse edge-inserted coefficient at
the `r-b` super-bond as a sum over triples of global virtual configurations agreeing away
from the red-to-blue crossings, with the bond-model-conjugated matrix coupling the two
red-to-blue crossing labels. This file collapses that sum to a constant times the
whole-bundle red inserted coefficient `TNLean.PEPS.redBundleInsertedCoeff` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite6`, the matrix-carrying analogue of the
closed-state collapse `TNLean.PEPS.agreeingTripleSum_collapse`.

The collapse is two-sided: the red configuration merges into the red boundary index `μ` of
the whole-bundle red inserted coefficient, while the blue and complement configurations
(agreeing on the blue-to-complement crossings) merge into the host boundary index `ν` over
`univ \ red`. The bond-model-conjugated matrix couples `μ` and `ν` through their
red-to-blue crossing labels.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 254--583 (the injective three-site comparison) and 1205--1210,
  1449--1500 (the blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The red-to-blue crossing label factors through the red boundary label

The bond-model-conjugated matrix in the relaxed-triple sum reads a global configuration only
through its red-to-blue crossing label, which is the red-to-blue crossing label of the
configuration's red boundary label. -/

omit [Fintype V] in
/-- The red-to-blue crossing label of a global configuration is the red-to-blue crossing
label of its red boundary label. -/
theorem crossingLabel_eq_redBoundaryRBCrossing (red blue : Finset V) (ζ : VirtualConfig A) :
    crossingLabel (G := G) A red blue ζ =
      redBoundaryRBCrossing (G := G) A red blue (regionBoundaryLabel (G := G) A red ζ) := by
  funext g
  rw [crossingLabel_apply, redBoundaryRBCrossing_apply, regionBoundaryLabel_apply]

variable [DecidableEq V]

/-! ### Geometric classification of red boundary crossings

Under the partition, a red boundary edge crosses to the blue region or to the complement.
A red-to-complement crossing edge is incident to the complement block, while a red-to-blue
crossing edge is not: its endpoints lie in the red and blue blocks, both disjoint from the
complement. These classify how the host-side merge along the complement reads each crossing
edge. -/

/-- A red-to-complement crossing edge is incident to the complement block. -/
theorem isRegionIncidentEdge_complement_of_crossing_rc
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {g : Edge G} (hg : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g) :
    IsRegionIncidentEdge (G := G) F.frame.complement g :=
  isRegionBoundaryEdge_touches (G := G) F.frame.complement hg.2

/-- A red-to-blue crossing edge is not incident to the complement block: its two endpoints
lie one in the red block and one in the blue block, both disjoint from the complement. -/
theorem not_isRegionIncidentEdge_complement_of_crossing_rb
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    {g : Edge G} (hg : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g) :
    ¬ IsRegionIncidentEdge (G := G) F.frame.complement g := by
  -- The red-to-blue crossing edge has, on each endpoint, a red and a blue boundary
  -- condition; the two combine to place each endpoint in red or in blue.
  have hcompl : ∀ v : V, v ∈ F.frame.red ∨ v ∈ F.frame.blue → v ∉ F.frame.complement := by
    rintro v (hr | hb) hc
    · exact (Finset.disjoint_left.mp hP.red_disjoint_complement) hr hc
    · exact (Finset.disjoint_left.mp hP.blue_disjoint_complement) hb hc
  rcases hg.1 with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ <;> rcases hg.2 with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · -- g.1.1 ∈ red, g.1.1 ∈ blue: impossible.
    exact absurd hb1 ((Finset.disjoint_left.mp hP.red_disjoint_blue) hr1)
  · -- g.1.1 ∈ red, g.1.2 ∈ blue.
    rintro (hc | hc)
    · exact hcompl _ (Or.inl hr1) hc
    · exact hcompl _ (Or.inr hb2) hc
  · -- g.1.2 ∈ red, g.1.1 ∈ blue.
    rintro (hc | hc)
    · exact hcompl _ (Or.inr hb1) hc
    · exact hcompl _ (Or.inl hr2) hc
  · -- g.1.2 ∈ red, g.1.2 ∈ blue: impossible.
    exact absurd hb2 ((Finset.disjoint_left.mp hP.red_disjoint_blue) hr2)

/-! ### The host merge of a relaxed triple's blue and complement configurations

The blue and complement configurations of a relaxed triple, agreeing on the
blue-to-complement crossings, merge into one host configuration over `univ \ red`: the
complement-incident edges read the complement configuration, the remaining edges the blue
configuration. The host vertex product of the merge reads the blue product against the
complement product, and the merge reads the original blue and complement configurations on
the host boundary through the red-to-blue and red-to-complement crossings respectively. -/

/-- The host configuration merging a relaxed triple's complement configuration `ζc` (on the
complement-incident edges) with its blue configuration `ζb` (elsewhere). This is the
complement-side `regionMerge` of the pair `(ζc, ζb)`. -/
noncomputable def hostMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζb ζc : VirtualConfig A) : VirtualConfig A :=
  regionMerge (G := G) A F.frame.complement (ζc, ζb)

omit [DecidableEq V] in
/-- The host merge reads the complement configuration on a complement-incident edge. -/
theorem hostMerge_complement (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {ζb ζc : VirtualConfig A} {e : Edge G}
    (he : IsRegionIncidentEdge (G := G) F.frame.complement e) :
    hostMerge F ζb ζc e = ζc e := by
  rw [hostMerge, regionMerge, if_pos he]

omit [DecidableEq V] in
/-- The host merge reads the blue configuration on an edge not incident to the complement. -/
theorem hostMerge_not_complement (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {ζb ζc : VirtualConfig A} {e : Edge G}
    (he : ¬ IsRegionIncidentEdge (G := G) F.frame.complement e) :
    hostMerge F ζb ζc e = ζb e := by
  rw [hostMerge, regionMerge, if_neg he]

/-- The complement vertex product of a relaxed triple reads the host merge unchanged:
complement-incident edges read the complement configuration. -/
theorem complProd_hostMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζb ζc : VirtualConfig A)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) :
    (∏ w : {w : V // w ∈ F.frame.complement}, A.component w.1 (fun ie => ζc ie.1) (σc w)) =
      ∏ w : {w : V // w ∈ F.frame.complement},
        A.component w.1 (fun ie => hostMerge F ζb ζc ie.1) (σc w) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1; funext ie
  have hcinc : IsRegionIncidentEdge (G := G) F.frame.complement ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (by rw [hie]; exact w.2)
    · exact Or.inr (by rw [hie]; exact w.2)
  rw [hostMerge_complement F hcinc]

/-- The blue vertex product of a relaxed triple agreeing on the blue-to-complement
crossings reads the host merge unchanged: a blue-incident edge that is also
complement-incident is a blue-to-complement crossing, where the agreement coincides. -/
theorem blueProd_hostMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {ζr ζb ζc : VirtualConfig A}
    (h : CrossTripleAgreesAwayRB F ζr ζb ζc)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue) :
    (∏ w : {w : V // w ∈ F.frame.blue}, A.component w.1 (fun ie => ζb ie.1) (σb w)) =
      ∏ w : {w : V // w ∈ F.frame.blue},
        A.component w.1 (fun ie => hostMerge F ζb ζc ie.1) (σb w) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1; funext ie
  have hbinc : IsRegionIncidentEdge (G := G) F.frame.blue ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (by rw [hie]; exact w.2)
    · exact Or.inr (by rw [hie]; exact w.2)
  by_cases hc : IsRegionIncidentEdge (G := G) F.frame.complement ie.1
  · -- A blue-incident, complement-incident edge is a blue-to-complement crossing.
    rw [hostMerge_complement F hc]
    have hbc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement ie.1 :=
      isCrossing_bc_of_incident F hP hbinc hc
    have := congrFun h.2 ⟨ie.1, hbc⟩
    simpa [crossingLabel] using this
  · rw [hostMerge_not_complement F hc]

/-- The host vertex product of the host merge, read with the fused blue/complement physical
leg, equals the relaxed triple's complement product against its blue product. -/
theorem hostProd_hostMerge_eq (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {ζr ζb ζc : VirtualConfig A}
    (h : CrossTripleAgreesAwayRB F ζr ζb ζc)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) :
    (∏ w : {w : V // w ∈ Finset.univ \ F.frame.red},
        A.component w.1 (fun ie => hostMerge F ζb ζc ie.1)
          ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc w)) =
      (∏ w : {w : V // w ∈ F.frame.complement}, A.component w.1 (fun ie => ζc ie.1) (σc w)) *
        ∏ w : {w : V // w ∈ F.frame.blue}, A.component w.1 (fun ie => ζb ie.1) (σb w) := by
  have hsplit := (F.frame.toThreeBlockGeometry hP).prod_sdiff_red_eq_blue_mul_complement
    (A := A) σb σc (hostMerge F ζb ζc)
  rw [complProd_hostMerge F ζb ζc σc, blueProd_hostMerge F hP h σb, mul_comm]
  exact hsplit

/-! ### The boundary labels and matrix coupling of the host merge

The red boundary label of a relaxed triple's red configuration and the red-reread host
boundary label of the host merge agree away from the red-to-blue crossings: a red boundary
edge not crossing to blue is a red-to-complement crossing, where the red-to-complement
agreement and the complement-incidence of the merge force the two labels to coincide. The
host merge's red-to-blue crossing label is the blue configuration's red-to-blue crossing
label, the second argument the bond-model-conjugated matrix reads. -/

/-- The red boundary label of `ζr` and the red-reread host boundary label of the host merge
agree away from the red-to-blue crossings. -/
theorem sameAwayFromRBBundle_hostMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {ζr ζb ζc : VirtualConfig A}
    (h : CrossTripleAgreesAwayRB F ζr ζb ζc) :
    SameAwayFromRBBundle (G := G) A F.frame.red F.frame.blue
      (regionBoundaryLabel (G := G) A F.frame.red ζr)
      (regionBoundaryLabel (G := G) A F.frame.red (hostMerge F ζb ζc)) := by
  intro f hf
  -- `f` is a red boundary edge not crossing to blue, hence a red-to-complement crossing.
  have hrc : IsCrossingEdge (G := G) A F.frame.red F.frame.complement f.1 := by
    refine ⟨f.2, ?_⟩
    -- The out-of-red endpoint lies in the complement (it is not in blue, else `f` would
    -- cross to blue).
    rcases f.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `f.1.1.1 ∈ red`, `f.1.1.2 ∉ red`. The out endpoint `f.1.1.2 ∈ complement`.
      have h2c : f.1.1.2 ∈ F.frame.complement := by
        have : f.1.1.2 ∈ F.frame.red ∪ F.frame.blue ∪ F.frame.complement := by
          rw [hP.cover_univ]; exact Finset.mem_univ _
        rcases Finset.mem_union.mp this with hrb | hc
        · rcases Finset.mem_union.mp hrb with hr | hb
          · exact absurd hr h2
          · exact absurd (⟨Or.inl ⟨h1, h2⟩,
              Or.inr ⟨(Finset.disjoint_left.mp hP.red_disjoint_blue) h1, hb⟩⟩ :
              IsCrossingEdge (G := G) A F.frame.red F.frame.blue f.1) hf
        · exact hc
      exact Or.inr ⟨(Finset.disjoint_left.mp hP.red_disjoint_complement) h1, h2c⟩
    · -- `f.1.1.1 ∉ red`, `f.1.1.2 ∈ red`. The out endpoint `f.1.1.1 ∈ complement`.
      have h1c : f.1.1.1 ∈ F.frame.complement := by
        have : f.1.1.1 ∈ F.frame.red ∪ F.frame.blue ∪ F.frame.complement := by
          rw [hP.cover_univ]; exact Finset.mem_univ _
        rcases Finset.mem_union.mp this with hrb | hc
        · rcases Finset.mem_union.mp hrb with hr | hb
          · exact absurd hr h1
          · exact absurd (⟨Or.inr ⟨h1, h2⟩,
              Or.inl ⟨hb, (Finset.disjoint_left.mp hP.red_disjoint_blue) h2⟩⟩ :
              IsCrossingEdge (G := G) A F.frame.red F.frame.blue f.1) hf
        · exact hc
      exact Or.inl ⟨h1c, (Finset.disjoint_left.mp hP.red_disjoint_complement) h2⟩
  -- On the red-to-complement crossing, `ζr = ζc` and the merge reads `ζc`.
  have hcinc : IsRegionIncidentEdge (G := G) F.frame.complement f.1 :=
    isRegionIncidentEdge_complement_of_crossing_rc F hrc
  rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply, hostMerge_complement F hcinc]
  have := congrFun h.1 ⟨f.1, hrc⟩
  simpa [crossingLabel] using this

/-- The red-to-blue crossing label of the host merge is the blue configuration's
red-to-blue crossing label, the second argument the bond-model-conjugated matrix reads. -/
theorem redBoundaryRBCrossing_hostMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (ζb ζc : VirtualConfig A) :
    redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
        (regionBoundaryLabel (G := G) A F.frame.red (hostMerge F ζb ζc)) =
      (fun g => ζb g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue) := by
  funext g
  rw [redBoundaryRBCrossing_apply, regionBoundaryLabel_apply,
    hostMerge_not_complement F (not_isRegionIncidentEdge_complement_of_crossing_rb F hP g.2)]

/-! ### The merged summand of a relaxed triple

Each relaxed-triple summand of the M-coupled three-region sum is the merged summand at the
two red boundary labels: the bond-model-conjugated matrix at the red and host merge boundary
labels' red-to-blue crossing labels, times the red vertex product, times the host vertex
product of the host merge against the fused blue/complement physical leg. -/

/-- **The merged summand of a relaxed triple.** A relaxed-triple summand equals the
bond-model-conjugated matrix at the two red boundary labels' red-to-blue crossing labels,
times the red vertex product of `ζr`, times the host vertex product of the host merge against
the fused blue/complement physical leg. -/
theorem relaxedTriple_summand_eq (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition)
    (M : Matrix (Fin (F.frame.coarseBondDim coarseEdgeRB))
      (Fin (F.frame.coarseBondDim coarseEdgeRB)) ℂ)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement)
    {ζr ζb ζc : VirtualConfig A} (h : CrossTripleAgreesAwayRB F ζr ζb ζc) :
    bondModelMatrix (G := G) F M
        (crossingLabel (G := G) A F.frame.red F.frame.blue ζr)
        (fun g => ζb g.1 : CrossingConfig (G := G) A F.frame.red F.frame.blue) *
        (∏ w : {w : V // w ∈ F.frame.red}, A.component w.1 (fun ie => ζr ie.1) (σr w)) *
        (∏ w : {w : V // w ∈ F.frame.complement},
          A.component w.1 (fun ie => ζc ie.1) (σc w)) *
        (∏ w : {w : V // w ∈ F.frame.blue}, A.component w.1 (fun ie => ζb ie.1) (σb w)) =
      bondModelMatrix (G := G) F M
          (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
            (regionBoundaryLabel (G := G) A F.frame.red ζr))
          (redBoundaryRBCrossing (G := G) A F.frame.red F.frame.blue
            (regionBoundaryLabel (G := G) A F.frame.red (hostMerge F ζb ζc))) *
        (∏ w : {w : V // w ∈ F.frame.red}, A.component w.1 (fun ie => ζr ie.1) (σr w)) *
        (∏ w : {w : V // w ∈ Finset.univ \ F.frame.red},
          A.component w.1 (fun ie => hostMerge F ζb ζc ie.1)
            ((F.frame.toThreeBlockGeometry hP).complPhysical σb σc w)) := by
  rw [crossingLabel_eq_redBoundaryRBCrossing, redBoundaryRBCrossing_hostMerge F hP ζb ζc,
    hostProd_hostMerge_eq F hP h σb σc]
  ring

/-! ### The host-merge fiber count

The relaxed pairs `(ζb, ζc)` agreeing on the blue-to-complement crossings whose host merge is
a fixed global configuration `η` biject with the free virtual indices: the complement
configuration is free on the edges not incident to the complement, and the blue configuration
is free on the complement-incident edges that are not blue-to-complement crossings (the
blue-to-complement crossings are pinned by the agreement). The common count is the product of
the complement's non-incident bond product and the bond product over the complement-incident
non-blue-to-complement-crossing edges. -/

/-- The bond-dimension product over the complement-incident edges that are not
blue-to-complement crossings: the free blue indices of the host-merge fiber. -/
noncomputable def hostBlueFreeBondProd (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) :
    ℕ :=
  ∏ e ∈ Finset.univ.filter (fun e : Edge G =>
      IsRegionIncidentEdge (G := G) F.frame.complement e ∧
        ¬ IsCrossingEdge (G := G) A F.frame.blue F.frame.complement e),
    A.bondDim e

/-- The host-merge fiber multiplicity: the complement non-incident bond product times the
free blue bond product. -/
noncomputable def hostMergeFiberProd (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) :
    ℕ :=
  regionNonIncidentBondProd A F.frame.complement * hostBlueFreeBondProd F

/-- The free virtual indices of a relaxed host-merge fiber: the complement configuration on
the edges not incident to the complement, and the blue configuration on the
complement-incident edges that are not blue-to-complement crossings. -/
abbrev HostFreeLegs (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) : Type _ :=
  ((e : {e : Edge G // ¬ IsRegionIncidentEdge (G := G) F.frame.complement e}) →
      Fin (A.bondDim e.1)) ×
  ((e : {e : Edge G // IsRegionIncidentEdge (G := G) F.frame.complement e ∧
        ¬ IsCrossingEdge (G := G) A F.frame.blue F.frame.complement e}) → Fin (A.bondDim e.1))

/-- The free virtual indices read off a relaxed host-merge fiber pair: the complement
configuration off the complement, the blue configuration on the free complement-incident
edges. -/
noncomputable def hostFiberLegs (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (p : VirtualConfig A × VirtualConfig A) : HostFreeLegs (G := G) F :=
  (fun e => p.2 e.1, fun e => p.1 e.1)

/-- Reconstruct a relaxed host-merge fiber pair from its free virtual indices and the merged
configuration `η`. The first component is the blue configuration: the merge `η` off the
complement, the agreement value `η` on the blue-to-complement crossings, the free index on
the remaining complement-incident edges. The second component is the complement
configuration: the merge `η` on the complement-incident edges, the free index off the
complement. -/
noncomputable def hostFiberPair (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (η : VirtualConfig A) (legs : HostFreeLegs (G := G) F) :
    VirtualConfig A × VirtualConfig A :=
  (fun e => if hc : IsRegionIncidentEdge (G := G) F.frame.complement e then
        (if hbc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement e then η e
          else legs.2 ⟨e, hc, hbc⟩)
      else η e,
   fun e => if hc : IsRegionIncidentEdge (G := G) F.frame.complement e then η e
      else legs.1 ⟨e, hc⟩)

/-- The free-index type of the relaxed host-merge fiber has the host-merge fiber product as
its cardinality. -/
theorem hostFreeLegs_card (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) :
    Fintype.card (HostFreeLegs (G := G) F) = hostMergeFiberProd F := by
  classical
  rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [hostMergeFiberProd, regionNonIncidentBondProd, hostBlueFreeBondProd,
    ← Finset.prod_subtype (Finset.univ.filter
        (fun e : Edge G => ¬ IsRegionIncidentEdge (G := G) F.frame.complement e))
      (fun e => by simp [Finset.mem_filter]) (fun e => A.bondDim e),
    ← Finset.prod_subtype (Finset.univ.filter
        (fun e : Edge G => IsRegionIncidentEdge (G := G) F.frame.complement e ∧
          ¬ IsCrossingEdge (G := G) A F.frame.blue F.frame.complement e))
      (fun e => by simp [Finset.mem_filter]) (fun e => A.bondDim e)]

/-- The blue-to-complement agreement of a relaxed pair, unpacked at a single
blue-to-complement crossing edge. -/
def HostPairAgrees (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζb ζc : VirtualConfig A) : Prop :=
  ∀ g : Edge G, IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g → ζb g = ζc g

instance (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (ζb ζc : VirtualConfig A) :
    Decidable (HostPairAgrees F ζb ζc) := by unfold HostPairAgrees; infer_instance

omit [DecidableEq V] in
/-- A blue-to-complement crossing edge is incident to the complement block. -/
theorem isRegionIncidentEdge_complement_of_crossing_bc
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {g : Edge G} (hg : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g) :
    IsRegionIncidentEdge (G := G) F.frame.complement g :=
  isRegionBoundaryEdge_touches (G := G) F.frame.complement hg.2

open scoped Classical in
/-- **The host-merge fiber count.** The relaxed pairs `(ζb, ζc)` agreeing on the
blue-to-complement crossings whose host merge is the fixed configuration `η` are in
bijection with the free virtual indices, so their number is the host-merge fiber product.
This is the host-side analogue of `TNLean.PEPS.triFiber_card`.

Source: arXiv:1804.04964, Section 3, lines 254--583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem hostMergeFiber_card (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        HostPairAgrees F p.1 p.2 ∧ hostMerge F p.1 p.2 = η)).card =
      hostMergeFiberProd F := by
  classical
  rw [← hostFreeLegs_card F, ← Finset.card_univ]
  refine Finset.card_nbij' (hostFiberLegs (G := G) F) (hostFiberPair (G := G) F η) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · -- The reconstruction lands in the fiber: agreement and merge identity.
    intro legs _
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · -- Agreement on the blue-to-complement crossings: both sides read `η`.
      intro g hg
      have hc : IsRegionIncidentEdge (G := G) F.frame.complement g :=
        isRegionIncidentEdge_complement_of_crossing_bc F hg
      simp only [hostFiberPair]
      rw [dif_pos hc, dif_pos hg, dif_pos hc]
    · -- The reconstruction merges back to `η`.
      funext e
      simp only [hostMerge, regionMerge, hostFiberPair]
      by_cases hc : IsRegionIncidentEdge (G := G) F.frame.complement e
      · rw [if_pos hc, dif_pos hc]
      · rw [if_neg hc, dif_neg hc]
  · -- Reconstructing from the free indices of a fiber pair recovers the pair.
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hagree, hmerge⟩ := hp
    -- `hostMerge p.1 p.2 = regionMerge complement (p.2, p.1)`: complement-incident reads
    -- `p.2`, the rest `p.1`.
    have hmerge' : ∀ e : Edge G,
        (if IsRegionIncidentEdge (G := G) F.frame.complement e then p.2 e else p.1 e) = η e := by
      intro e; have := congrFun hmerge e; rwa [hostMerge, regionMerge] at this
    refine Prod.ext ?_ ?_
    · -- First component (the blue configuration `p.1`).
      funext e
      simp only [hostFiberPair, hostFiberLegs]
      by_cases hc : IsRegionIncidentEdge (G := G) F.frame.complement e
      · rw [dif_pos hc]
        by_cases hbc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement e
        · -- On a blue-to-complement crossing the agreement and merge force `p.1 e = η e`.
          rw [dif_pos hbc]
          have h1 := hmerge' e; rw [if_pos hc] at h1
          rw [hagree e hbc, h1]
        · rw [dif_neg hbc]
      · rw [dif_neg hc]
        have := hmerge' e; rw [if_neg hc] at this; exact this.symm
    · -- Second component (the complement configuration `p.2`).
      funext e
      simp only [hostFiberPair, hostFiberLegs]
      by_cases hc : IsRegionIncidentEdge (G := G) F.frame.complement e
      · rw [dif_pos hc]
        have := hmerge' e; rw [if_pos hc] at this; exact this.symm
      · rw [dif_neg hc]
  · -- Reading the free indices of a reconstruction recovers them.
    intro legs _
    obtain ⟨lc, lb⟩ := legs
    refine Prod.ext ?_ ?_
    · funext e
      simp only [hostFiberLegs, hostFiberPair]
      rw [dif_neg e.2]
    · funext e
      simp only [hostFiberLegs, hostFiberPair]
      obtain ⟨hc, hbc⟩ := e.2
      rw [dif_pos hc, dif_neg hbc]

/-! ### The host-merge fiberwise collapse

A sum over relaxed pairs agreeing on the blue-to-complement crossings, of a quantity reading
the pair only through its host merge, collapses to the host-merge fiber product times the
sum of that quantity over all global configurations. -/

open scoped Classical in
/-- **The host-merge fiberwise collapse.** A sum over the relaxed pairs agreeing on the
blue-to-complement crossings, of a quantity `g` reading the pair only through its host merge,
collapses to the host-merge fiber product times the sum of `g` over all global virtual
configurations.

Source: arXiv:1804.04964, Section 3, lines 254--583 of `Papers/1804.04964/paper_normal.tex`. -/
theorem hostMerge_fiberwise_collapse (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (g : VirtualConfig A → ℂ) :
    (∑ p ∈ Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        HostPairAgrees F p.1 p.2), g (hostMerge F p.1 p.2)) =
      hostMergeFiberProd F • ∑ η : VirtualConfig A, g η := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ.filter
      (fun p : VirtualConfig A × VirtualConfig A => HostPairAgrees F p.1 p.2))
    (fun p => hostMerge F p.1 p.2) (fun p => g (hostMerge F p.1 p.2))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  rw [Finset.filter_filter,
    Finset.sum_congr rfl (g := fun _ => g η)
      (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
    Finset.sum_const, hostMergeFiber_card F η]

end PEPS
end TNLean
