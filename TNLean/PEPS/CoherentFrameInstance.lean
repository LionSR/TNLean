import TNLean.PEPS.RegionBlock.CoarseThreeSite11
import TNLean.PEPS.NormalEdgeBlockingData
import TNLean.PEPS.RegionBlock.UnionClosure

/-!
# The coherent coarse blocking frame of a one-edge blocking datum

The coarse three-site route of `TNLean.PEPS.RegionBlock.CoarseThreeSite11` delivers
the per-edge gauge through the interface
`TNLean.PEPS.exists_regionEdgeGauge_of_coherentFrames`, whose input is a
`CoherentCoarseBlockingFrame` at each tensor sharing the three regions, the bond
dimensions, and the single distinguished crossing edge.  Building that frame from
the source's finite-lattice blocking is the geometry obligation recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

This file builds the frame from a one-edge blocking datum
(`TNLean.PEPS.NormalEdgeBlockingData`) over the concrete region-injectivity
predicate of a tensor (`regionInjectivityDataOf A`).  The three regions and their
blocked-tensor injectivities come directly from the datum; the partition geometry
(pairwise disjointness and coverage) comes from the datum's disjointness and cover
fields.  The coarse super-bonds carry the original inter-region crossing
configurations through the canonical fintype enumeration, and each super-site's leg
identification is assembled from the two bond models on its incident super-edges
through the boundary-edge partition of its region (every boundary edge of a region
crosses to exactly one partner region).  With the leg identifications built this way
the six factoring fields hold definitionally.

The single-crossing hypothesis `IsCrossingEdge A red blue g ↔ g = e` is the
coordinate computation supplied separately by the lattice geometry; here it is a
plain hypothesis.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1449--1500 of `Papers/1804.04964/paper_normal.tex` (the three
  injective regions around an edge partition the lattice)](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### Enumeration of the incident super-edges

Each coarse super-site has exactly two incident super-edges
(`TNLean.PEPS.RegionBlock.CoarseThreeSite3`).  The case lemmas below name them and
support the leg-pair equivalences that split a per-super-site leg assignment into
its two incident super-bond values. -/

/-- An incident super-edge of the red super-site is `r-b` or `r-c`. -/
theorem incident0_cases (ie : IncidentEdge coarseGraph 0) :
    ie = incidentRB0 ∨ ie = incidentRC0 := by
  obtain ⟨e, he⟩ := ie
  rcases coarse_edge_cases e with h | h | h <;> subst h
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (show False by rcases he with h | h <;> simp [coarseEdgeBC] at h) id

/-- An incident super-edge of the blue super-site is `r-b` or `b-c`. -/
theorem incident1_cases (ie : IncidentEdge coarseGraph 1) :
    ie = incidentRB1 ∨ ie = incidentBC1 := by
  obtain ⟨e, he⟩ := ie
  rcases coarse_edge_cases e with h | h | h <;> subst h
  · exact Or.inl rfl
  · exact absurd (show False by rcases he with h | h <;> simp [coarseEdgeRC] at h) id
  · exact Or.inr rfl

/-- An incident super-edge of the complement super-site is `r-c` or `b-c`. -/
theorem incident2_cases (ie : IncidentEdge coarseGraph 2) :
    ie = incidentRC2 ∨ ie = incidentBC2 := by
  obtain ⟨e, he⟩ := ie
  rcases coarse_edge_cases e with h | h | h <;> subst h
  · exact absurd (show False by rcases he with h | h <;> simp [coarseEdgeRB] at h) id
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ### Leg-pair equivalences

A leg assignment of a super-site is a function on its two incident super-edges, so
it identifies with the pair of its values on those two super-edges. -/

/-- A red super-site leg assignment is the pair of its `r-b` and `r-c` values. -/
noncomputable def legPair0 {cbd : Edge coarseGraph → ℕ} :
    ((ie : IncidentEdge coarseGraph 0) → Fin (cbd ie.1)) ≃
      (Fin (cbd coarseEdgeRB) × Fin (cbd coarseEdgeRC)) where
  toFun legs := (legs incidentRB0, legs incidentRC0)
  invFun p := fun ie =>
    if h : ie = incidentRB0 then h ▸ p.1
    else ((incident0_cases ie).resolve_left h) ▸ p.2
  left_inv legs := by
    funext ie; dsimp only
    rcases incident0_cases ie with h | h <;> subst h
    · rw [dif_pos rfl]
    · rw [dif_neg (show incidentRC0 ≠ incidentRB0 by decide)]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · dsimp only; rw [dif_pos rfl]
    · dsimp only; rw [dif_neg (show incidentRC0 ≠ incidentRB0 by decide)]

/-- A blue super-site leg assignment is the pair of its `r-b` and `b-c` values. -/
noncomputable def legPair1 {cbd : Edge coarseGraph → ℕ} :
    ((ie : IncidentEdge coarseGraph 1) → Fin (cbd ie.1)) ≃
      (Fin (cbd coarseEdgeRB) × Fin (cbd coarseEdgeBC)) where
  toFun legs := (legs incidentRB1, legs incidentBC1)
  invFun p := fun ie =>
    if h : ie = incidentRB1 then h ▸ p.1
    else ((incident1_cases ie).resolve_left h) ▸ p.2
  left_inv legs := by
    funext ie; dsimp only
    rcases incident1_cases ie with h | h <;> subst h
    · rw [dif_pos rfl]
    · rw [dif_neg (show incidentBC1 ≠ incidentRB1 by decide)]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · dsimp only; rw [dif_pos rfl]
    · dsimp only; rw [dif_neg (show incidentBC1 ≠ incidentRB1 by decide)]

/-- A complement super-site leg assignment is the pair of its `r-c` and `b-c` values. -/
noncomputable def legPair2 {cbd : Edge coarseGraph → ℕ} :
    ((ie : IncidentEdge coarseGraph 2) → Fin (cbd ie.1)) ≃
      (Fin (cbd coarseEdgeRC) × Fin (cbd coarseEdgeBC)) where
  toFun legs := (legs incidentRC2, legs incidentBC2)
  invFun p := fun ie =>
    if h : ie = incidentRC2 then h ▸ p.1
    else ((incident2_cases ie).resolve_left h) ▸ p.2
  left_inv legs := by
    funext ie; dsimp only
    rcases incident2_cases ie with h | h <;> subst h
    · rw [dif_pos rfl]
    · rw [dif_neg (show incidentBC2 ≠ incidentRC2 by decide)]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · dsimp only; rw [dif_pos rfl]
    · dsimp only; rw [dif_neg (show incidentBC2 ≠ incidentRC2 by decide)]

@[simp] theorem legPair0_apply_fst {cbd : Edge coarseGraph → ℕ}
    (legs : (ie : IncidentEdge coarseGraph 0) → Fin (cbd ie.1)) :
    (legPair0 legs).1 = legs incidentRB0 := rfl
@[simp] theorem legPair0_apply_snd {cbd : Edge coarseGraph → ℕ}
    (legs : (ie : IncidentEdge coarseGraph 0) → Fin (cbd ie.1)) :
    (legPair0 legs).2 = legs incidentRC0 := rfl
@[simp] theorem legPair1_apply_fst {cbd : Edge coarseGraph → ℕ}
    (legs : (ie : IncidentEdge coarseGraph 1) → Fin (cbd ie.1)) :
    (legPair1 legs).1 = legs incidentRB1 := rfl
@[simp] theorem legPair1_apply_snd {cbd : Edge coarseGraph → ℕ}
    (legs : (ie : IncidentEdge coarseGraph 1) → Fin (cbd ie.1)) :
    (legPair1 legs).2 = legs incidentBC1 := rfl
@[simp] theorem legPair2_apply_fst {cbd : Edge coarseGraph → ℕ}
    (legs : (ie : IncidentEdge coarseGraph 2) → Fin (cbd ie.1)) :
    (legPair2 legs).1 = legs incidentRC2 := rfl
@[simp] theorem legPair2_apply_snd {cbd : Edge coarseGraph → ℕ}
    (legs : (ie : IncidentEdge coarseGraph 2) → Fin (cbd ie.1)) :
    (legPair2 legs).2 = legs incidentBC2 := rfl

/-! ### Crossing exclusivity at a super-site

Under the partition the two crossing classes at a super-site are exclusive: a
boundary edge crossing to one partner region does not cross to the other, because
the two partner regions are disjoint.  These lemmas make the boundary-edge
partition of a region a genuine dichotomy. -/

namespace CoarseBlockingFrame

variable (F : CoarseBlockingFrame (G := G) (d := d) A)

/-- A red boundary edge crossing to blue does not cross to the complement. -/
theorem not_crossing_rb_and_rc (hP : F.IsPartition) {g : Edge G}
    (hrb : IsCrossingEdge (G := G) A F.red F.blue g) :
    ¬ IsCrossingEdge (G := G) A F.red F.complement g := by
  intro hrc
  rcases hrb.1 with ⟨h1r, _⟩ | ⟨_, h2r⟩
  · have hb2 : g.1.2 ∈ F.blue := by
      rcases hrb.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (Finset.disjoint_left.mp hP.red_disjoint_blue h1r)
      · exact hb
    have hc2 : g.1.2 ∈ F.complement := by
      rcases hrc.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (Finset.disjoint_left.mp hP.red_disjoint_complement h1r)
      · exact hb
    exact Finset.disjoint_left.mp hP.blue_disjoint_complement hb2 hc2
  · have hb1 : g.1.1 ∈ F.blue := by
      rcases hrb.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact ha
      · exact absurd hb (Finset.disjoint_left.mp hP.red_disjoint_blue h2r)
    have hc1 : g.1.1 ∈ F.complement := by
      rcases hrc.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact ha
      · exact absurd hb (Finset.disjoint_left.mp hP.red_disjoint_complement h2r)
    exact Finset.disjoint_left.mp hP.blue_disjoint_complement hb1 hc1

/-- A blue boundary edge crossing to red does not cross to the complement. -/
theorem not_crossing_rb_and_bc (hP : F.IsPartition) {g : Edge G}
    (hrb : IsCrossingEdge (G := G) A F.red F.blue g) :
    ¬ IsCrossingEdge (G := G) A F.blue F.complement g := by
  intro hbc
  rcases hrb.1 with ⟨h1r, _⟩ | ⟨_, h2r⟩
  · have hb2 : g.1.2 ∈ F.blue := by
      rcases hrb.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (Finset.disjoint_left.mp hP.red_disjoint_blue h1r)
      · exact hb
    have hc2 : g.1.2 ∈ F.complement := by
      rcases hbc.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (Finset.disjoint_left.mp hP.red_disjoint_complement h1r)
      · exact hb
    exact Finset.disjoint_left.mp hP.blue_disjoint_complement hb2 hc2
  · have hb1 : g.1.1 ∈ F.blue := by
      rcases hrb.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact ha
      · exact absurd hb (Finset.disjoint_left.mp hP.red_disjoint_blue h2r)
    have hc1 : g.1.1 ∈ F.complement := by
      rcases hbc.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact ha
      · exact absurd hb (Finset.disjoint_left.mp hP.red_disjoint_complement h2r)
    exact Finset.disjoint_left.mp hP.blue_disjoint_complement hb1 hc1

/-- A complement boundary edge crossing to red does not cross to blue. -/
theorem not_crossing_rc_and_bc (hP : F.IsPartition) {g : Edge G}
    (hrc : IsCrossingEdge (G := G) A F.red F.complement g) :
    ¬ IsCrossingEdge (G := G) A F.blue F.complement g := by
  intro hbc
  rcases hrc.1 with ⟨h1r, _⟩ | ⟨_, h2r⟩
  · have hc2 : g.1.2 ∈ F.complement := by
      rcases hrc.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (Finset.disjoint_left.mp hP.red_disjoint_complement h1r)
      · exact hb
    have hb2 : g.1.2 ∈ F.blue := by
      rcases hbc.1 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact absurd ha (Finset.disjoint_left.mp hP.red_disjoint_blue h1r)
      · exact hb
    exact Finset.disjoint_left.mp hP.blue_disjoint_complement hb2 hc2
  · have hc1 : g.1.1 ∈ F.complement := by
      rcases hrc.2 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact ha
      · exact absurd hb (Finset.disjoint_left.mp hP.red_disjoint_complement h2r)
    have hb1 : g.1.1 ∈ F.blue := by
      rcases hbc.1 with ⟨ha, _⟩ | ⟨_, hb⟩
      · exact ha
      · exact absurd hb (Finset.disjoint_left.mp hP.red_disjoint_blue h2r)
    exact Finset.disjoint_left.mp hP.blue_disjoint_complement hb1 hc1

/-! ### Boundary-edge split of a region

Every boundary edge of a region crosses to exactly one partner region
(`isCrossingEdge_red_blue_or_red_complement` and its siblings), so a region
boundary configuration splits into its two crossing configurations. -/

open scoped Classical in
/-- The red boundary configuration splits into its `r-b` and `r-c` crossing
configurations. -/
noncomputable def redBoundaryEquiv (hP : F.IsPartition) :
    RegionBoundaryConfig (G := G) A F.red ≃
      (CrossingConfig (G := G) A F.red F.blue ×
        CrossingConfig (G := G) A F.red F.complement) where
  toFun μ := (fun g => μ ⟨g.1, g.2.1⟩, fun g => μ ⟨g.1, g.2.1⟩)
  invFun p := fun b =>
    if hb : IsCrossingEdge (G := G) A F.red F.blue b.1 then p.1 ⟨b.1, hb⟩
    else p.2 ⟨b.1, (F.isCrossingEdge_red_blue_or_red_complement hP b.2).resolve_left hb⟩
  left_inv μ := by
    funext b; dsimp only
    by_cases hb : IsCrossingEdge (G := G) A F.red F.blue b.1
    · rw [dif_pos hb]
    · rw [dif_neg hb]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext g; dsimp only; rw [dif_pos g.2]
    · funext g; dsimp only
      rw [dif_neg (fun hrb => F.not_crossing_rb_and_rc hP hrb g.2)]

open scoped Classical in
/-- The blue boundary configuration splits into its `r-b` and `b-c` crossing
configurations.  The `r-b` crossing of blue is the symmetric image of the `r-b`
crossing of red. -/
noncomputable def blueBoundaryEquiv (hP : F.IsPartition) :
    RegionBoundaryConfig (G := G) A F.blue ≃
      (CrossingConfig (G := G) A F.red F.blue ×
        CrossingConfig (G := G) A F.blue F.complement) where
  toFun μ := (fun g => μ ⟨g.1, g.2.2⟩, fun g => μ ⟨g.1, g.2.1⟩)
  invFun p := fun b =>
    if hb : IsCrossingEdge (G := G) A F.red F.blue b.1 then p.1 ⟨b.1, hb⟩
    else p.2 ⟨b.1, (F.isCrossingEdge_red_blue_or_blue_complement hP b.2).resolve_left hb⟩
  left_inv μ := by
    funext b; dsimp only
    by_cases hb : IsCrossingEdge (G := G) A F.red F.blue b.1
    · rw [dif_pos hb]
    · rw [dif_neg hb]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext g; dsimp only; rw [dif_pos g.2]
    · funext g; dsimp only
      rw [dif_neg (fun hrb => F.not_crossing_rb_and_bc hP hrb g.2)]

open scoped Classical in
/-- The complement boundary configuration splits into its `r-c` and `b-c` crossing
configurations.  Both are the symmetric images of the red-to-complement and
blue-to-complement crossings. -/
noncomputable def complementBoundaryEquiv (hP : F.IsPartition) :
    RegionBoundaryConfig (G := G) A F.complement ≃
      (CrossingConfig (G := G) A F.red F.complement ×
        CrossingConfig (G := G) A F.blue F.complement) where
  toFun μ := (fun g => μ ⟨g.1, g.2.2⟩, fun g => μ ⟨g.1, g.2.2⟩)
  invFun p := fun b =>
    if hb : IsCrossingEdge (G := G) A F.red F.complement b.1 then p.1 ⟨b.1, hb⟩
    else p.2 ⟨b.1, (F.isCrossingEdge_red_complement_or_blue_complement hP b.2).resolve_left hb⟩
  left_inv μ := by
    funext b; dsimp only
    by_cases hb : IsCrossingEdge (G := G) A F.red F.complement b.1
    · rw [dif_pos hb]
    · rw [dif_neg hb]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext g; dsimp only; rw [dif_pos g.2]
    · funext g; dsimp only
      rw [dif_neg (fun hrc => F.not_crossing_rc_and_bc hP hrc g.2)]

end CoarseBlockingFrame

end PEPS
end TNLean
