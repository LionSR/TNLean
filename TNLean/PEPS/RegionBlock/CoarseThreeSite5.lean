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

end PEPS
end TNLean
