import TNLean.PEPS.RegionBlock.CoarseThreeSite4

/-!
# The three-region merge collapse for the normal PEPS theorem

The coarse state sum of `TNLean.PEPS.RegionBlock.CoarseThreeSite4` is reindexed, by
the bond models, as a sum over triples of global virtual configurations agreeing on
the crossing edges of the product of the three regions' vertex products
(`threeRegionSum_eq_agreeingTripleSum`). This file collapses that triple sum to a
constant times the original closed-state coefficient.

The collapse mirrors the landed two-block fiber collapse
`TNLean.PEPS.stateCoeff_eq_regionComplement`: an agreeing triple
`(ζ_red, ζ_blue, ζ_compl)` is merged into one global configuration reading the
red-incident edges from `ζ_red`, the remaining blue-incident edges from `ζ_blue`, and
the rest from `ζ_compl`. The three regions' vertex products read this merged
configuration unchanged, and the fiber over a merged configuration is parameterised by
the virtual indices each configuration is free to choose away from its region: the
product of the three regions' non-incident bond products.

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
variable {A : Tensor G d}

/-! ### Per-edge agreement of an agreeing triple

The crossing-label agreement of a triple, unpacked at a single crossing edge: the two
configurations crossing that edge carry the same virtual index there. These are the
per-edge facts the merge product equalities consume. -/

omit [DecidableEq V] in
/-- On a red-to-blue crossing edge, an agreeing triple's red and blue configurations
coincide. -/
theorem TripleAgrees.rb (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {ζr ζb ζc : VirtualConfig A} (h : TripleAgrees F ζr ζb ζc)
    {e : Edge G} (he : IsCrossingEdge (G := G) A F.frame.red F.frame.blue e) :
    ζr e = ζb e := by
  have := congrFun h.1 ⟨e, he⟩; simpa [crossingLabel] using this

omit [DecidableEq V] in
/-- On a red-to-complement crossing edge, an agreeing triple's red and complement
configurations coincide. -/
theorem TripleAgrees.rc (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {ζr ζb ζc : VirtualConfig A} (h : TripleAgrees F ζr ζb ζc)
    {e : Edge G} (he : IsCrossingEdge (G := G) A F.frame.red F.frame.complement e) :
    ζr e = ζc e := by
  have := congrFun h.2.1 ⟨e, he⟩; simpa [crossingLabel] using this

omit [DecidableEq V] in
/-- On a blue-to-complement crossing edge, an agreeing triple's blue and complement
configurations coincide. -/
theorem TripleAgrees.bc (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    {ζr ζb ζc : VirtualConfig A} (h : TripleAgrees F ζr ζb ζc)
    {e : Edge G} (he : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement e) :
    ζb e = ζc e := by
  have := congrFun h.2.2 ⟨e, he⟩; simpa [crossingLabel] using this

/-! ### Two-region incident edges are crossing edges

An edge incident to two of the three regions crosses between them: its two endpoints
lie one in each. These classify which configuration the merge reads on an edge shared
by two regions, where the agreement forces the two configurations to coincide. -/

/-- An edge incident to both red and blue is a red-to-blue crossing edge. -/
theorem isCrossing_rb_of_incident (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {e : Edge G}
    (hr : IsRegionIncidentEdge (G := G) F.frame.red e)
    (hb : IsRegionIncidentEdge (G := G) F.frame.blue e) :
    IsCrossingEdge (G := G) A F.frame.red F.frame.blue e := by
  rcases hr with hr1 | hr2 <;> rcases hb with hb1 | hb2
  · exact absurd hb1 ((Finset.disjoint_left.mp hP.red_disjoint_blue) hr1)
  · exact ⟨Or.inl ⟨hr1, (Finset.disjoint_right.mp hP.red_disjoint_blue) hb2⟩,
      Or.inr ⟨(Finset.disjoint_left.mp hP.red_disjoint_blue) hr1, hb2⟩⟩
  · exact ⟨Or.inr ⟨(Finset.disjoint_right.mp hP.red_disjoint_blue) hb1, hr2⟩,
      Or.inl ⟨hb1, (Finset.disjoint_left.mp hP.red_disjoint_blue) hr2⟩⟩
  · exact absurd hb2 ((Finset.disjoint_left.mp hP.red_disjoint_blue) hr2)

/-- An edge incident to both red and complement is a red-to-complement crossing edge. -/
theorem isCrossing_rc_of_incident (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {e : Edge G}
    (hr : IsRegionIncidentEdge (G := G) F.frame.red e)
    (hc : IsRegionIncidentEdge (G := G) F.frame.complement e) :
    IsCrossingEdge (G := G) A F.frame.red F.frame.complement e := by
  rcases hr with hr1 | hr2 <;> rcases hc with hc1 | hc2
  · exact absurd hc1 ((Finset.disjoint_left.mp hP.red_disjoint_complement) hr1)
  · exact ⟨Or.inl ⟨hr1, (Finset.disjoint_right.mp hP.red_disjoint_complement) hc2⟩,
      Or.inr ⟨(Finset.disjoint_left.mp hP.red_disjoint_complement) hr1, hc2⟩⟩
  · exact ⟨Or.inr ⟨(Finset.disjoint_right.mp hP.red_disjoint_complement) hc1, hr2⟩,
      Or.inl ⟨hc1, (Finset.disjoint_left.mp hP.red_disjoint_complement) hr2⟩⟩
  · exact absurd hc2 ((Finset.disjoint_left.mp hP.red_disjoint_complement) hr2)

/-- An edge incident to both blue and complement is a blue-to-complement crossing edge. -/
theorem isCrossing_bc_of_incident (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {e : Edge G}
    (hb : IsRegionIncidentEdge (G := G) F.frame.blue e)
    (hc : IsRegionIncidentEdge (G := G) F.frame.complement e) :
    IsCrossingEdge (G := G) A F.frame.blue F.frame.complement e := by
  rcases hb with hb1 | hb2 <;> rcases hc with hc1 | hc2
  · exact absurd hc1 ((Finset.disjoint_left.mp hP.blue_disjoint_complement) hb1)
  · exact ⟨Or.inl ⟨hb1, (Finset.disjoint_right.mp hP.blue_disjoint_complement) hc2⟩,
      Or.inr ⟨(Finset.disjoint_left.mp hP.blue_disjoint_complement) hb1, hc2⟩⟩
  · exact ⟨Or.inr ⟨(Finset.disjoint_right.mp hP.blue_disjoint_complement) hc1, hb2⟩,
      Or.inl ⟨hc1, (Finset.disjoint_left.mp hP.blue_disjoint_complement) hb2⟩⟩
  · exact absurd hc2 ((Finset.disjoint_left.mp hP.blue_disjoint_complement) hb2)

/-! ### The three-way merge

The merge of an agreeing triple reads the red-incident edges from the red
configuration, the remaining blue-incident edges from the blue configuration, and the
rest from the complement configuration. Each region's vertex product reads the merge
unchanged: on an edge incident to a second region the crossing agreement forces the
two configurations to coincide. -/

/-- **The three-way merge.** The global virtual configuration reading red-incident
edges from `ζr`, the remaining blue-incident edges from `ζb`, and the rest from `ζc`. -/
def triMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζb ζc : VirtualConfig A) : VirtualConfig A :=
  fun e => if IsRegionIncidentEdge (G := G) F.frame.red e then ζr e
    else if IsRegionIncidentEdge (G := G) F.frame.blue e then ζb e
    else ζc e

omit [DecidableEq V] in
/-- The red vertex product reads the merge unchanged: red-incident edges read `ζr`. -/
theorem redProd_triMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (ζr ζb ζc : VirtualConfig A)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red) :
    (∏ w : {w : V // w ∈ F.frame.red}, A.component w.1 (fun ie => ζr ie.1) (σr w)) =
      ∏ w : {w : V // w ∈ F.frame.red},
        A.component w.1 (fun ie => triMerge F ζr ζb ζc ie.1) (σr w) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1; funext ie
  have hrinc : IsRegionIncidentEdge (G := G) F.frame.red ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (by rw [hie]; exact w.2)
    · exact Or.inr (by rw [hie]; exact w.2)
  rw [triMerge, if_pos hrinc]

/-- The blue vertex product reads the merge unchanged: a blue-incident edge that is
also red-incident is a red-to-blue crossing edge, where the agreement coincides. -/
theorem blueProd_triMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {ζr ζb ζc : VirtualConfig A} (h : TripleAgrees F ζr ζb ζc)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue) :
    (∏ w : {w : V // w ∈ F.frame.blue}, A.component w.1 (fun ie => ζb ie.1) (σb w)) =
      ∏ w : {w : V // w ∈ F.frame.blue},
        A.component w.1 (fun ie => triMerge F ζr ζb ζc ie.1) (σb w) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1; funext ie
  have hbinc : IsRegionIncidentEdge (G := G) F.frame.blue ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (by rw [hie]; exact w.2)
    · exact Or.inr (by rw [hie]; exact w.2)
  rw [triMerge]
  by_cases hr : IsRegionIncidentEdge (G := G) F.frame.red ie.1
  · rw [if_pos hr]; exact (h.rb F (isCrossing_rb_of_incident F hP hr hbinc)).symm
  · rw [if_neg hr, if_pos hbinc]

/-- The complement vertex product reads the merge unchanged: a complement-incident
edge that is red-incident is a red-to-complement crossing edge, and one that is
blue-incident but not red-incident is a blue-to-complement crossing edge, where the
respective agreements coincide. -/
theorem complProd_triMerge (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {ζr ζb ζc : VirtualConfig A} (h : TripleAgrees F ζr ζb ζc)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) :
    (∏ w : {w : V // w ∈ F.frame.complement}, A.component w.1 (fun ie => ζc ie.1) (σc w)) =
      ∏ w : {w : V // w ∈ F.frame.complement},
        A.component w.1 (fun ie => triMerge F ζr ζb ζc ie.1) (σc w) := by
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1; funext ie
  have hcinc : IsRegionIncidentEdge (G := G) F.frame.complement ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (by rw [hie]; exact w.2)
    · exact Or.inr (by rw [hie]; exact w.2)
  rw [triMerge]
  by_cases hr : IsRegionIncidentEdge (G := G) F.frame.red ie.1
  · rw [if_pos hr]; exact (h.rc F (isCrossing_rc_of_incident F hP hr hcinc)).symm
  · rw [if_neg hr]
    by_cases hb : IsRegionIncidentEdge (G := G) F.frame.blue ie.1
    · rw [if_pos hb]; exact (h.bc F (isCrossing_bc_of_incident F hP hb hcinc)).symm
    · rw [if_neg hb]

/-! ### The assembled physical configuration

The three regions' physical legs glue into one global physical configuration: each
vertex reads its own region's leg (red, then blue, then complement, under the
partition). The closed-state coefficient of the assembled configuration is the sum
over global virtual configurations of the merged summand. -/

/-- **The assembled physical configuration.** A global physical configuration reading
the red leg on red vertices, the blue leg on blue vertices, and the complement leg on
complement vertices. -/
def assembleTri (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) : V → Fin d :=
  fun w => if hr : w ∈ F.frame.red then σr ⟨w, hr⟩
    else if hb : w ∈ F.frame.blue then σb ⟨w, hb⟩
    else σc ⟨w, by
      have : w ∈ F.frame.red ∪ F.frame.blue ∪ F.frame.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact absurd h hr
        · exact absurd h hb
      · exact h⟩

@[simp] theorem assembleTri_red (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement)
    (w : {w : V // w ∈ F.frame.red}) :
    assembleTri F hP σr σb σc w.1 = σr w := by rw [assembleTri, dif_pos w.2]

@[simp] theorem assembleTri_blue (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement)
    (w : {w : V // w ∈ F.frame.blue}) :
    assembleTri F hP σr σb σc w.1 = σb w := by
  have hnr : w.1 ∉ F.frame.red := fun hr =>
    (Finset.disjoint_left.mp hP.red_disjoint_blue) hr w.2
  rw [assembleTri, dif_neg hnr, dif_pos w.2]

@[simp] theorem assembleTri_compl (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement)
    (w : {w : V // w ∈ F.frame.complement}) :
    assembleTri F hP σr σb σc w.1 = σc w := by
  have hnr : w.1 ∉ F.frame.red := fun hr =>
    (Finset.disjoint_left.mp hP.red_disjoint_complement) hr w.2
  have hnb : w.1 ∉ F.frame.blue := fun hb =>
    (Finset.disjoint_left.mp hP.blue_disjoint_complement) hb w.2
  rw [assembleTri, dif_neg hnr, dif_neg hnb]

/-- The global vertex product of the assembled physical configuration splits as the
product of the three regions' vertex products, at any fixed global virtual
configuration. -/
theorem prod_assembleTri_split (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) (η : VirtualConfig A) :
    (∏ v : V, A.component v (fun ie => η ie.1) (assembleTri F hP σr σb σc v)) =
      (∏ w : {w : V // w ∈ F.frame.red}, A.component w.1 (fun ie => η ie.1) (σr w)) *
        (∏ w : {w : V // w ∈ F.frame.blue}, A.component w.1 (fun ie => η ie.1) (σb w)) *
        (∏ w : {w : V // w ∈ F.frame.complement},
          A.component w.1 (fun ie => η ie.1) (σc w)) := by
  classical
  rw [show (Finset.univ : Finset V) = F.frame.red ∪ F.frame.blue ∪ F.frame.complement from
      hP.cover_univ.symm,
    Finset.prod_union (by
      rw [Finset.disjoint_union_left]
      exact ⟨hP.red_disjoint_complement, hP.blue_disjoint_complement⟩),
    Finset.prod_union hP.red_disjoint_blue]
  congr 1
  · congr 1
    · rw [Finset.prod_subtype F.frame.red (fun x => Iff.rfl)
        (fun v => A.component v (fun ie => η ie.1) (assembleTri F hP σr σb σc v))]
      exact Finset.prod_congr rfl (fun w _ => by rw [assembleTri_red])
    · rw [Finset.prod_subtype F.frame.blue (fun x => Iff.rfl)
        (fun v => A.component v (fun ie => η ie.1) (assembleTri F hP σr σb σc v))]
      exact Finset.prod_congr rfl (fun w _ => by rw [assembleTri_blue])
  · rw [Finset.prod_subtype F.frame.complement (fun x => Iff.rfl)
      (fun v => A.component v (fun ie => η ie.1) (assembleTri F hP σr σb σc v))]
    exact Finset.prod_congr rfl (fun w _ => by rw [assembleTri_compl])

/-- The merged summand at a global virtual configuration: the product of the three
regions' vertex products, all read from the one configuration. -/
noncomputable def triMergedSummand (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) (η : VirtualConfig A) : ℂ :=
  (∏ w : {w : V // w ∈ F.frame.red}, A.component w.1 (fun ie => η ie.1) (σr w)) *
    (∏ w : {w : V // w ∈ F.frame.blue}, A.component w.1 (fun ie => η ie.1) (σb w)) *
    (∏ w : {w : V // w ∈ F.frame.complement}, A.component w.1 (fun ie => η ie.1) (σc w))

/-- The sum of the merged summands over all global virtual configurations is the
closed-state coefficient of the assembled physical configuration. -/
theorem sum_triMergedSummand (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) :
    (∑ η : VirtualConfig A, triMergedSummand F σr σb σc η) =
      stateCoeff A (assembleTri F hP σr σb σc) := by
  classical
  unfold stateCoeff triMergedSummand
  exact Finset.sum_congr rfl (fun η _ => (prod_assembleTri_split F hP σr σb σc η).symm)

/-! ### The fiber count

The agreeing triples merging to a fixed global configuration are parameterised by the
virtual indices each configuration is free to choose away from its region: an agreeing
triple in the fiber reads the merge on every region-incident edge, and the crossing
agreements pin the shared edges, leaving free the values of each configuration on the
edges not incident to its own region. The common count of these free indices is the
product of the three regions' non-incident bond products. -/

/-- The bond-dimension product over the edges not incident to `R`: the multiplicity of
free virtual indices a configuration carries away from its own region. -/
noncomputable def regionNonIncidentBondProd (A : Tensor G d) (R : Finset V) : ℕ :=
  ∏ e ∈ Finset.univ.filter (fun e : Edge G => ¬ IsRegionIncidentEdge (G := G) R e),
    A.bondDim e

/-- An edge incident to neither red nor blue is incident to the complement: under the
partition both its endpoints lie in the complement. -/
theorem complIncident_of_not_red_not_blue (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) {e : Edge G}
    (hr : ¬ IsRegionIncidentEdge (G := G) F.frame.red e)
    (hb : ¬ IsRegionIncidentEdge (G := G) F.frame.blue e) :
    IsRegionIncidentEdge (G := G) F.frame.complement e := by
  have h1nr : e.1.1 ∉ F.frame.red := fun h => hr (Or.inl h)
  have h1nb : e.1.1 ∉ F.frame.blue := fun h => hb (Or.inl h)
  have h1c : e.1.1 ∈ F.frame.complement := by
    have : e.1.1 ∈ F.frame.red ∪ F.frame.blue ∪ F.frame.complement := by
      rw [hP.cover_univ]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp this with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact absurd h h1nr
      · exact absurd h h1nb
    · exact h
  exact Or.inl h1c

/-- The free virtual indices of an agreeing triple in a fiber: each configuration's
values on the edges not incident to its own region. -/
abbrev FreeLegs (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) : Type _ :=
  ((e : {e : Edge G // ¬ IsRegionIncidentEdge (G := G) F.frame.red e}) → Fin (A.bondDim e.1)) ×
  ((e : {e : Edge G // ¬ IsRegionIncidentEdge (G := G) F.frame.blue e}) → Fin (A.bondDim e.1)) ×
  ((e : {e : Edge G // ¬ IsRegionIncidentEdge (G := G) F.frame.complement e}) →
    Fin (A.bondDim e.1))

/-- The free virtual indices read off a triple: each configuration restricted to the
edges not incident to its own region. -/
noncomputable def triFiberLegs (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (p : VirtualConfig A × VirtualConfig A × VirtualConfig A) : FreeLegs F :=
  (fun e => p.1 e.1, fun e => p.2.1 e.1, fun e => p.2.2 e.1)

/-- Reconstruct a fiber triple from its free virtual indices and the merged
configuration: each configuration reads the merge on its region-incident edges and the
free indices elsewhere. -/
noncomputable def triFiberTriple (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (η : VirtualConfig A) (legs : FreeLegs F) :
    VirtualConfig A × VirtualConfig A × VirtualConfig A :=
  (fun e => if hr : IsRegionIncidentEdge (G := G) F.frame.red e then η e else legs.1 ⟨e, hr⟩,
   fun e => if hb : IsRegionIncidentEdge (G := G) F.frame.blue e then η e else legs.2.1 ⟨e, hb⟩,
   fun e => if hc : IsRegionIncidentEdge (G := G) F.frame.complement e then η e
              else legs.2.2 ⟨e, hc⟩)

/-- The free-index type has the product of the three regions' non-incident bond
products as its cardinality. -/
theorem freeLegs_card (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) :
    Fintype.card (FreeLegs F) =
      regionNonIncidentBondProd A F.frame.red * regionNonIncidentBondProd A F.frame.blue *
        regionNonIncidentBondProd A F.frame.complement := by
  classical
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_pi, Fintype.card_pi, Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [regionNonIncidentBondProd, regionNonIncidentBondProd, regionNonIncidentBondProd,
    ← Finset.prod_subtype (Finset.univ.filter
        (fun e : Edge G => ¬ IsRegionIncidentEdge (G := G) F.frame.red e))
      (fun e => by simp [Finset.mem_filter]) (fun e => A.bondDim e),
    ← Finset.prod_subtype (Finset.univ.filter
        (fun e : Edge G => ¬ IsRegionIncidentEdge (G := G) F.frame.blue e))
      (fun e => by simp [Finset.mem_filter]) (fun e => A.bondDim e),
    ← Finset.prod_subtype (Finset.univ.filter
        (fun e : Edge G => ¬ IsRegionIncidentEdge (G := G) F.frame.complement e))
      (fun e => by simp [Finset.mem_filter]) (fun e => A.bondDim e)]
  ring

open scoped Classical in
/-- **The fiber count.** The agreeing triples merging to a fixed global configuration
`η` are in bijection with the free virtual indices, so their number is the product of
the three regions' non-incident bond products. This is the three-region analogue of
`TNLean.PEPS.regionFiber_card`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem triFiber_card (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A × VirtualConfig A =>
        TripleAgrees F p.1 p.2.1 p.2.2 ∧ triMerge F p.1 p.2.1 p.2.2 = η)).card =
      regionNonIncidentBondProd A F.frame.red * regionNonIncidentBondProd A F.frame.blue *
        regionNonIncidentBondProd A F.frame.complement := by
  classical
  rw [← freeLegs_card F, ← Finset.card_univ]
  refine Finset.card_nbij' (triFiberLegs F) (triFiberTriple F η) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · -- The reconstruction lands in the fiber: agreement and merge identity.
    intro legs _
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · funext g
      simp only [crossingLabel, triFiberTriple]
      have hr : IsRegionIncidentEdge (G := G) F.frame.red g.1 :=
        isRegionBoundaryEdge_touches (G := G) F.frame.red g.2.1
      have hb : IsRegionIncidentEdge (G := G) F.frame.blue g.1 :=
        isRegionBoundaryEdge_touches (G := G) F.frame.blue g.2.2
      rw [dif_pos hr, dif_pos hb]
    · funext g
      simp only [crossingLabel, triFiberTriple]
      have hr : IsRegionIncidentEdge (G := G) F.frame.red g.1 :=
        isRegionBoundaryEdge_touches (G := G) F.frame.red g.2.1
      have hc : IsRegionIncidentEdge (G := G) F.frame.complement g.1 :=
        isRegionBoundaryEdge_touches (G := G) F.frame.complement g.2.2
      rw [dif_pos hr, dif_pos hc]
    · funext g
      simp only [crossingLabel, triFiberTriple]
      have hb : IsRegionIncidentEdge (G := G) F.frame.blue g.1 :=
        isRegionBoundaryEdge_touches (G := G) F.frame.blue g.2.1
      have hc : IsRegionIncidentEdge (G := G) F.frame.complement g.1 :=
        isRegionBoundaryEdge_touches (G := G) F.frame.complement g.2.2
      rw [dif_pos hb, dif_pos hc]
    · funext e
      simp only [triMerge, triFiberTriple]
      by_cases hr : IsRegionIncidentEdge (G := G) F.frame.red e
      · rw [if_pos hr, dif_pos hr]
      · rw [if_neg hr]
        by_cases hb : IsRegionIncidentEdge (G := G) F.frame.blue e
        · rw [if_pos hb, dif_pos hb]
        · rw [if_neg hb, dif_pos (complIncident_of_not_red_not_blue F hP hr hb)]
  · -- Reconstructing from the free indices of a fiber triple recovers the triple.
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hag, hmerge⟩ := hp
    have hmerge' : ∀ e, triMerge F p.1 p.2.1 p.2.2 e = η e := fun e => congrFun hmerge e
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext e
      simp only [triFiberTriple, triFiberLegs]
      by_cases hr : IsRegionIncidentEdge (G := G) F.frame.red e
      · rw [dif_pos hr]
        have := hmerge' e; rw [triMerge, if_pos hr] at this; exact this.symm
      · rw [dif_neg hr]
    · funext e
      simp only [triFiberTriple, triFiberLegs]
      by_cases hb : IsRegionIncidentEdge (G := G) F.frame.blue e
      · rw [dif_pos hb]
        by_cases hr : IsRegionIncidentEdge (G := G) F.frame.red e
        · have := hmerge' e; rw [triMerge, if_pos hr] at this
          rw [← (hag.rb F (isCrossing_rb_of_incident F hP hr hb)), this]
        · have := hmerge' e; rw [triMerge, if_neg hr, if_pos hb] at this; exact this.symm
      · rw [dif_neg hb]
    · funext e
      simp only [triFiberTriple, triFiberLegs]
      by_cases hc : IsRegionIncidentEdge (G := G) F.frame.complement e
      · rw [dif_pos hc]
        by_cases hr : IsRegionIncidentEdge (G := G) F.frame.red e
        · have := hmerge' e; rw [triMerge, if_pos hr] at this
          rw [← (hag.rc F (isCrossing_rc_of_incident F hP hr hc)), this]
        · by_cases hb : IsRegionIncidentEdge (G := G) F.frame.blue e
          · have := hmerge' e; rw [triMerge, if_neg hr, if_pos hb] at this
            rw [← (hag.bc F (isCrossing_bc_of_incident F hP hb hc)), this]
          · have := hmerge' e; rw [triMerge, if_neg hr, if_neg hb] at this; exact this.symm
      · rw [dif_neg hc]
  · -- Reading the free indices of a reconstruction recovers them.
    intro legs _
    obtain ⟨lr, lb, lc⟩ := legs
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext e; simp only [triFiberLegs, triFiberTriple]; rw [dif_neg e.2]
    · funext e; simp only [triFiberLegs, triFiberTriple]; rw [dif_neg e.2]
    · funext e; simp only [triFiberLegs, triFiberTriple]; rw [dif_neg e.2]

/-! ### The three-region merge collapse

The agreeing-triple sum collapses to a constant times the closed-state coefficient of
the assembled physical configuration: each agreeing triple's product is the merged
summand at its merge, grouping by the merge counts each merged summand with the fiber
multiplicity, and the merged summands sum to the closed-state coefficient. -/

/-- An agreeing triple's product of region vertex products is the merged summand at its
three-way merge. -/
theorem agreeing_summand_eq (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement)
    {ζr ζb ζc : VirtualConfig A} (h : TripleAgrees F ζr ζb ζc) :
    (∏ w : {w : V // w ∈ F.frame.red}, A.component w.1 (fun ie => ζr ie.1) (σr w)) *
        (∏ w : {w : V // w ∈ F.frame.blue}, A.component w.1 (fun ie => ζb ie.1) (σb w)) *
        (∏ w : {w : V // w ∈ F.frame.complement},
          A.component w.1 (fun ie => ζc ie.1) (σc w)) =
      triMergedSummand F σr σb σc (triMerge F ζr ζb ζc) := by
  rw [triMergedSummand, ← redProd_triMerge F ζr ζb ζc σr,
    ← blueProd_triMerge F hP h σb, ← complProd_triMerge F hP h σc]

open scoped Classical in
/-- **The three-region merge collapse.** The agreeing-triple sum of the product of the
three regions' vertex products collapses to the product of the three regions'
non-incident bond products, times the closed-state coefficient of the assembled
physical configuration. This is the three-region analogue of
`TNLean.PEPS.stateCoeff_eq_regionComplement`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem agreeingTripleSum_collapse (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition)
    (σr : RegionPhysicalConfig (V := V) (d := d) F.frame.red)
    (σb : RegionPhysicalConfig (V := V) (d := d) F.frame.blue)
    (σc : RegionPhysicalConfig (V := V) (d := d) F.frame.complement) :
    (∑ t ∈ (Finset.univ : Finset (VirtualConfig A × VirtualConfig A × VirtualConfig A)).filter
        (fun t => TripleAgrees F t.1 t.2.1 t.2.2),
      (∏ w : {w : V // w ∈ F.frame.red},
          A.component w.1 (fun ie => t.1 ie.1) (σr w)) *
        (∏ w : {w : V // w ∈ F.frame.blue},
          A.component w.1 (fun ie => t.2.1 ie.1) (σb w)) *
        (∏ w : {w : V // w ∈ F.frame.complement},
          A.component w.1 (fun ie => t.2.2 ie.1) (σc w))) =
      (regionNonIncidentBondProd A F.frame.red * regionNonIncidentBondProd A F.frame.blue *
          regionNonIncidentBondProd A F.frame.complement) •
        stateCoeff A (assembleTri F hP σr σb σc) := by
  classical
  rw [Finset.sum_congr rfl (fun t ht => agreeing_summand_eq F hP σr σb σc
    (by rw [Finset.mem_filter] at ht; exact ht.2))]
  -- Group by merged configuration, count each fiber, and reassemble the closed state.
  conv_lhs => rw [← Finset.sum_fiberwise (Finset.univ.filter
    (fun t : VirtualConfig A × VirtualConfig A × VirtualConfig A =>
      TripleAgrees F t.1 t.2.1 t.2.2))
    (fun t => triMerge F t.1 t.2.1 t.2.2)
    (fun t => triMergedSummand F σr σb σc (triMerge F t.1 t.2.1 t.2.2))]
  rw [← sum_triMergedSummand F hP σr σb σc, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  rw [Finset.filter_filter,
    Finset.sum_congr rfl (g := fun _ => triMergedSummand F σr σb σc η)
      (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
    Finset.sum_const, triFiber_card F hP η]

open scoped Classical in
/-- **The global fiber-collapse bijection.** The closed-state coefficient of the coarse
three-site tensor at a coarse physical configuration `s` equals the product of the
three regions' non-incident bond products, times the closed-state coefficient of the
original tensor at the assembled physical configuration that decodes `s` to each
region.

The coarse state sum is written through the coherent bond models as a triple sum over
coarse virtual configurations of the three region weights' product
(`stateCoeff_coarseTensor_eq_threeRegionSum`), reindexed by the bond models as a sum
over agreeing crossing triples (`threeRegionSum_eq_agreeingTripleSum`), and collapsed
by merging each agreeing triple into one global configuration with the three regions'
non-incident bond products as fiber multiplicity (`agreeingTripleSum_collapse`).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1205--1210 and
1449--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem stateCoeff_coarseTensor_collapse (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (hP : F.frame.IsPartition) (s : Fin 3 → Fin (coarseDim V d)) :
    stateCoeff (F.frame.coarseTensor) s =
      (regionNonIncidentBondProd A F.frame.red * regionNonIncidentBondProd A F.frame.blue *
          regionNonIncidentBondProd A F.frame.complement) •
        stateCoeff A (assembleTri F hP
          (coarseProj F.frame.red (s 0)) (coarseProj F.frame.blue (s 1))
          (coarseProj F.frame.complement (s 2))) := by
  rw [F.frame.stateCoeff_coarseTensor_eq_threeRegionSum s,
    threeRegionSum_eq_agreeingTripleSum F hP s,
    agreeingTripleSum_collapse F hP
      (coarseProj F.frame.red (s 0)) (coarseProj F.frame.blue (s 1))
      (coarseProj F.frame.complement (s 2))]

/-! ### Same-state transport to the coarse tensors

The assembled physical configuration depends only on the three regions, not on the
tensor, so two coherent frames sharing the same regions assemble the same global
physical configurations. With matched bond dimensions the merge-collapse constants
coincide, so the same-state hypothesis transports to equality of the coarse states. -/

/-- The assembled physical configuration depends only on the three regions: at each
vertex it reads the decoded coarse physical index of the region containing it. -/
theorem assembleTri_eq_decode {A : Tensor G d}
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A) (hP : F.frame.IsPartition)
    (s : Fin 3 → Fin (coarseDim V d)) (w : V) :
    assembleTri F hP (coarseProj F.frame.red (s 0)) (coarseProj F.frame.blue (s 1))
        (coarseProj F.frame.complement (s 2)) w =
      if w ∈ F.frame.red then coarseDecode V d (s 0) w
      else if w ∈ F.frame.blue then coarseDecode V d (s 1) w
      else coarseDecode V d (s 2) w := by
  rw [assembleTri]
  by_cases hr : w ∈ F.frame.red
  · rw [dif_pos hr, if_pos hr]; rfl
  · rw [dif_neg hr, if_neg hr]
    by_cases hb : w ∈ F.frame.blue
    · rw [dif_pos hb, if_pos hb]; rfl
    · rw [dif_neg hb, if_neg hb]; rfl

open scoped Classical in
/-- **Same-state transport to the coarse tensors.** Two coherent frames over tensors
`A` and `B` sharing the same three regions and bond dimensions, with `A` and `B`
generating the same state, give coarse three-site tensors generating the same coarse
state: the merge-collapse constants coincide and the assembled physical configurations
agree, so the original same-state hypothesis transports through the collapse.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem coarseTensor_sameState_of_sameState {A B : Tensor G d}
    (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)
    (F' : CoherentCoarseBlockingFrame (G := G) (d := d) B)
    (hP : F.frame.IsPartition) (hP' : F'.frame.IsPartition)
    (hred : F.frame.red = F'.frame.red) (hblue : F.frame.blue = F'.frame.blue)
    (hcompl : F.frame.complement = F'.frame.complement)
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) :
    SameState (F.frame.coarseTensor) (F'.frame.coarseTensor) := by
  intro s
  rw [stateCoeff_coarseTensor_collapse F hP s, stateCoeff_coarseTensor_collapse F' hP' s]
  have hconst : regionNonIncidentBondProd A F.frame.red *
        regionNonIncidentBondProd A F.frame.blue *
        regionNonIncidentBondProd A F.frame.complement =
      regionNonIncidentBondProd B F'.frame.red *
        regionNonIncidentBondProd B F'.frame.blue *
        regionNonIncidentBondProd B F'.frame.complement := by
    rw [regionNonIncidentBondProd, regionNonIncidentBondProd, regionNonIncidentBondProd,
      regionNonIncidentBondProd, regionNonIncidentBondProd, regionNonIncidentBondProd,
      hred, hblue, hcompl, hbond]
  rw [hconst]
  congr 1
  rw [hAB]
  congr 1
  funext w
  rw [assembleTri_eq_decode, assembleTri_eq_decode, hred, hblue]

end PEPS
end TNLean
