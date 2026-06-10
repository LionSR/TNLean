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

variable {V : Type*} [Fintype V] [LinearOrder V]
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

end CoarseBlockingFrame

/-! ### Region-level crossing classification

The crossing classification of a region boundary edge depends only on the three
regions' disjointness and coverage, not on the leg identifications of a frame.  The
region-level statements below let the frame constructor build its boundary splits
before the frame exists.  Their proofs are the partition geometry of
`TNLean.PEPS.RegionBlock.CoarseThreeSite3` read off a placeholder frame whose leg
identifications are immaterial. -/

variable {red blue complement : Finset V}

/-- A red boundary edge crosses to blue or to the complement. -/
theorem crossing_red_blue_or_red_complement
    (hrb : Disjoint red blue) (hrc : Disjoint red complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ)
    {g : Edge G} (hg : IsRegionBoundaryEdge (G := G) red g) :
    IsCrossingEdge (G := G) A red blue g ∨ IsCrossingEdge (G := G) A red complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1nb : g.1.1 ∉ blue := Finset.disjoint_left.mp hrb h1
    have h1nc : g.1.1 ∉ complement := Finset.disjoint_left.mp hrc h1
    have hmem : g.1.2 ∈ blue ∨ g.1.2 ∈ complement := by
      have : g.1.2 ∈ red ∪ blue ∪ complement := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with hrb' | hc
      · rcases Finset.mem_union.mp hrb' with hr | hbl
        · exact absurd hr h2
        · exact Or.inl hbl
      · exact Or.inr hc
    rcases hmem with hb | hc
    · exact Or.inl ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nb, hb⟩⟩
    · exact Or.inr ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nc, hc⟩⟩
  · have h2nb : g.1.2 ∉ blue := Finset.disjoint_left.mp hrb h2
    have h2nc : g.1.2 ∉ complement := Finset.disjoint_left.mp hrc h2
    have hmem : g.1.1 ∈ blue ∨ g.1.1 ∈ complement := by
      have : g.1.1 ∈ red ∪ blue ∪ complement := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with hrb' | hc
      · rcases Finset.mem_union.mp hrb' with hr | hbl
        · exact absurd hr h1
        · exact Or.inl hbl
      · exact Or.inr hc
    rcases hmem with hb | hc
    · exact Or.inl ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hb, h2nb⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hc, h2nc⟩⟩

/-- A blue boundary edge crosses to red or to the complement. -/
theorem crossing_red_blue_or_blue_complement
    (hrb : Disjoint red blue) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ)
    {g : Edge G} (hg : IsRegionBoundaryEdge (G := G) blue g) :
    IsCrossingEdge (G := G) A red blue g ∨ IsCrossingEdge (G := G) A blue complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1nr : g.1.1 ∉ red := Finset.disjoint_right.mp hrb h1
    have h1nc : g.1.1 ∉ complement := Finset.disjoint_left.mp hbc h1
    have hmem : g.1.2 ∈ red ∨ g.1.2 ∈ complement := by
      have : g.1.2 ∈ red ∪ blue ∪ complement := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with hrb' | hc
      · rcases Finset.mem_union.mp hrb' with hr | hbl
        · exact Or.inl hr
        · exact absurd hbl h2
      · exact Or.inr hc
    rcases hmem with hr | hc
    · exact Or.inl ⟨Or.inr ⟨h1nr, hr⟩, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nc, hc⟩⟩
  · have h2nr : g.1.2 ∉ red := Finset.disjoint_right.mp hrb h2
    have h2nc : g.1.2 ∉ complement := Finset.disjoint_left.mp hbc h2
    have hmem : g.1.1 ∈ red ∨ g.1.1 ∈ complement := by
      have : g.1.1 ∈ red ∪ blue ∪ complement := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with hrb' | hc
      · rcases Finset.mem_union.mp hrb' with hr | hbl
        · exact Or.inl hr
        · exact absurd hbl h1
      · exact Or.inr hc
    rcases hmem with hr | hc
    · exact Or.inl ⟨Or.inl ⟨hr, h2nr⟩, Or.inr ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hc, h2nc⟩⟩

/-- A complement boundary edge crosses to red or to blue. -/
theorem crossing_red_complement_or_blue_complement
    (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ)
    {g : Edge G} (hg : IsRegionBoundaryEdge (G := G) complement g) :
    IsCrossingEdge (G := G) A red complement g ∨ IsCrossingEdge (G := G) A blue complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1nr : g.1.1 ∉ red := Finset.disjoint_right.mp hrc h1
    have h1nb : g.1.1 ∉ blue := Finset.disjoint_right.mp hbc h1
    have hmem : g.1.2 ∈ red ∨ g.1.2 ∈ blue := by
      have : g.1.2 ∈ red ∪ blue ∪ complement := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with hrb' | hc
      · rcases Finset.mem_union.mp hrb' with hr | hbl
        · exact Or.inl hr
        · exact Or.inr hbl
      · exact absurd hc h2
    rcases hmem with hr | hb
    · exact Or.inl ⟨Or.inr ⟨h1nr, hr⟩, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1nb, hb⟩, Or.inl ⟨h1, h2⟩⟩
  · have h2nr : g.1.2 ∉ red := Finset.disjoint_right.mp hrc h2
    have h2nb : g.1.2 ∉ blue := Finset.disjoint_right.mp hbc h2
    have hmem : g.1.1 ∈ red ∨ g.1.1 ∈ blue := by
      have : g.1.1 ∈ red ∪ blue ∪ complement := by rw [hcover]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with hrb' | hc
      · rcases Finset.mem_union.mp hrb' with hr | hbl
        · exact Or.inl hr
        · exact Or.inr hbl
      · exact absurd hc h1
    rcases hmem with hr | hb
    · exact Or.inl ⟨Or.inl ⟨hr, h2nr⟩, Or.inr ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inl ⟨hb, h2nb⟩, Or.inr ⟨h1, h2⟩⟩

/-! ### Region-level crossing exclusivity

The out-of-region endpoint of a boundary edge lies in exactly one partner region,
so a boundary edge crossing to one partner does not cross to the other.  These make
the boundary split a genuine dichotomy. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- A partner-region membership of the out-of-red endpoint of a red boundary edge.
If `g` is a boundary edge of `red` and also a boundary edge of a region `S`
disjoint from `red`, then the out-of-red endpoint of `g` lies in `S`. -/
theorem partner_mem_of_crossing {S : Finset V} (hrS : Disjoint red S) {g : Edge G}
    (hred : IsRegionBoundaryEdge (G := G) red g) (hS : IsRegionBoundaryEdge (G := G) S g) :
    (g.1.1 ∉ red ∧ g.1.1 ∈ S) ∨ (g.1.2 ∉ red ∧ g.1.2 ∈ S) := by
  rcases hred with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
  · -- g.1.1 ∈ red, g.1.2 ∉ red: the out-of-red endpoint is g.1.2.
    refine Or.inr ⟨hr2, ?_⟩
    rcases hS with ⟨hs1, _⟩ | ⟨_, hs2⟩
    · exact absurd hs1 (Finset.disjoint_left.mp hrS hr1)
    · exact hs2
  · -- g.1.1 ∉ red, g.1.2 ∈ red: the out-of-red endpoint is g.1.1.
    refine Or.inl ⟨hr1, ?_⟩
    rcases hS with ⟨hs1, _⟩ | ⟨_, hs2⟩
    · exact hs1
    · exact absurd hs2 (Finset.disjoint_left.mp hrS hr2)

omit [Fintype V] in
/-- A red boundary edge crossing to blue does not cross to the complement. -/
theorem not_crossing_red_blue_red_complement
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    {g : Edge G} (h1 : IsCrossingEdge (G := G) A red blue g)
    (h2 : IsCrossingEdge (G := G) A red complement g) : False := by
  -- The out-of-red endpoint of `g`, fixed by the red-boundary structure, lies in
  -- blue (from `h1`) and in complement (from `h2`).
  rcases h1.1 with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
  · have hb : g.1.2 ∈ blue :=
      ((partner_mem_of_crossing hrb h1.1 h1.2).resolve_left (fun hh => hh.1 hr1)).2
    have hc : g.1.2 ∈ complement :=
      ((partner_mem_of_crossing hrc h2.1 h2.2).resolve_left (fun hh => hh.1 hr1)).2
    exact Finset.disjoint_left.mp hbc hb hc
  · have hb : g.1.1 ∈ blue :=
      ((partner_mem_of_crossing hrb h1.1 h1.2).resolve_right (fun hh => hh.1 hr2)).2
    have hc : g.1.1 ∈ complement :=
      ((partner_mem_of_crossing hrc h2.1 h2.2).resolve_right (fun hh => hh.1 hr2)).2
    exact Finset.disjoint_left.mp hbc hb hc

omit [Fintype V] in
/-- A blue boundary edge crossing to red does not cross to the complement. -/
theorem not_crossing_red_blue_blue_complement
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    {g : Edge G} (h1 : IsCrossingEdge (G := G) A red blue g)
    (h2 : IsCrossingEdge (G := G) A blue complement g) : False := by
  rcases h1.2 with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
  · have hr : g.1.2 ∈ red :=
      ((partner_mem_of_crossing hrb.symm h1.2 h1.1).resolve_left (fun hh => hh.1 hb1)).2
    have hc : g.1.2 ∈ complement :=
      ((partner_mem_of_crossing hbc h2.1 h2.2).resolve_left (fun hh => hh.1 hb1)).2
    exact Finset.disjoint_left.mp hrc hr hc
  · have hr : g.1.1 ∈ red :=
      ((partner_mem_of_crossing hrb.symm h1.2 h1.1).resolve_right (fun hh => hh.1 hb2)).2
    have hc : g.1.1 ∈ complement :=
      ((partner_mem_of_crossing hbc h2.1 h2.2).resolve_right (fun hh => hh.1 hb2)).2
    exact Finset.disjoint_left.mp hrc hr hc

omit [Fintype V] in
/-- A complement boundary edge crossing to red does not cross to blue. -/
theorem not_crossing_red_complement_blue_complement
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    {g : Edge G} (h1 : IsCrossingEdge (G := G) A red complement g)
    (h2 : IsCrossingEdge (G := G) A blue complement g) : False := by
  rcases h1.2 with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
  · have hr : g.1.2 ∈ red :=
      ((partner_mem_of_crossing hrc.symm h1.2 h1.1).resolve_left (fun hh => hh.1 hc1)).2
    have hb : g.1.2 ∈ blue :=
      ((partner_mem_of_crossing hbc.symm h2.2 h2.1).resolve_left (fun hh => hh.1 hc1)).2
    exact Finset.disjoint_left.mp hrb hr hb
  · have hr : g.1.1 ∈ red :=
      ((partner_mem_of_crossing hrc.symm h1.2 h1.1).resolve_right (fun hh => hh.1 hc2)).2
    have hb : g.1.1 ∈ blue :=
      ((partner_mem_of_crossing hbc.symm h2.2 h2.1).resolve_right (fun hh => hh.1 hc2)).2
    exact Finset.disjoint_left.mp hrb hr hb

/-! ### Region-level boundary splits

Each region's boundary configuration splits into its two crossing configurations.
These are the leg identifications built before the frame exists. -/

open scoped Classical in
/-- The red boundary configuration splits into its `r-b` and `r-c` crossing
configurations. -/
noncomputable def redBoundaryEquivOf
    (hrb : Disjoint red blue) (hrc : Disjoint red complement)
    (hbc : Disjoint blue complement) (hcover : red ∪ blue ∪ complement = Finset.univ) :
    RegionBoundaryConfig (G := G) A red ≃
      (CrossingConfig (G := G) A red blue × CrossingConfig (G := G) A red complement) where
  toFun μ := (fun g => μ ⟨g.1, g.2.1⟩, fun g => μ ⟨g.1, g.2.1⟩)
  invFun p := fun b =>
    if hb : IsCrossingEdge (G := G) A red blue b.1 then p.1 ⟨b.1, hb⟩
    else p.2 ⟨b.1, (crossing_red_blue_or_red_complement hrb hrc hcover b.2).resolve_left hb⟩
  left_inv μ := by
    funext b; dsimp only
    by_cases hb : IsCrossingEdge (G := G) A red blue b.1
    · rw [dif_pos hb]
    · rw [dif_neg hb]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext g; dsimp only; rw [dif_pos g.2]
    · funext g; dsimp only
      rw [dif_neg fun hb => not_crossing_red_blue_red_complement hrb hrc hbc hb g.2]

open scoped Classical in
/-- The blue boundary configuration splits into its `r-b` and `b-c` crossing
configurations. -/
noncomputable def blueBoundaryEquivOf
    (hrb : Disjoint red blue) (hrc : Disjoint red complement)
    (hbc : Disjoint blue complement) (hcover : red ∪ blue ∪ complement = Finset.univ) :
    RegionBoundaryConfig (G := G) A blue ≃
      (CrossingConfig (G := G) A red blue × CrossingConfig (G := G) A blue complement) where
  toFun μ := (fun g => μ ⟨g.1, g.2.2⟩, fun g => μ ⟨g.1, g.2.1⟩)
  invFun p := fun b =>
    if hb : IsCrossingEdge (G := G) A red blue b.1 then p.1 ⟨b.1, hb⟩
    else p.2 ⟨b.1, (crossing_red_blue_or_blue_complement hrb hbc hcover b.2).resolve_left hb⟩
  left_inv μ := by
    funext b; dsimp only
    by_cases hb : IsCrossingEdge (G := G) A red blue b.1
    · rw [dif_pos hb]
    · rw [dif_neg hb]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext g; dsimp only; rw [dif_pos g.2]
    · funext g; dsimp only
      rw [dif_neg fun hb => not_crossing_red_blue_blue_complement hrb hrc hbc hb g.2]

open scoped Classical in
/-- The complement boundary configuration splits into its `r-c` and `b-c` crossing
configurations. -/
noncomputable def complementBoundaryEquivOf
    (hrb : Disjoint red blue) (hrc : Disjoint red complement)
    (hbc : Disjoint blue complement) (hcover : red ∪ blue ∪ complement = Finset.univ) :
    RegionBoundaryConfig (G := G) A complement ≃
      (CrossingConfig (G := G) A red complement × CrossingConfig (G := G) A blue complement) where
  toFun μ := (fun g => μ ⟨g.1, g.2.2⟩, fun g => μ ⟨g.1, g.2.2⟩)
  invFun p := fun b =>
    if hb : IsCrossingEdge (G := G) A red complement b.1 then p.1 ⟨b.1, hb⟩
    else p.2 ⟨b.1, (crossing_red_complement_or_blue_complement hrc hbc hcover b.2).resolve_left hb⟩
  left_inv μ := by
    funext b; dsimp only
    by_cases hb : IsCrossingEdge (G := G) A red complement b.1
    · rw [dif_pos hb]
    · rw [dif_neg hb]
  right_inv p := by
    obtain ⟨a, b⟩ := p
    refine Prod.ext ?_ ?_
    · funext g; dsimp only; rw [dif_pos g.2]
    · funext g; dsimp only
      rw [dif_neg fun hc => not_crossing_red_complement_blue_complement hrb hrc hbc hc g.2]

/-! ### The canonical coarse bond dimensions and bond models

The coarse super-bond of a super-edge carries the original inter-region crossing
configurations between the two incident regions.  The canonical choice takes the
coarse bond dimension to be the cardinality of that crossing-configuration type and
the bond model to be the canonical fintype enumeration.  Under positive bond
dimensions the crossing-configuration type is nonempty, so the coarse bond
dimensions are positive. -/

/-- The canonical coarse bond dimension on a super-edge: the cardinality of the
crossing configurations between the two incident regions, with the regions read off
the super-edge's two endpoints through `![red, blue, complement]`. -/
noncomputable def coarseBondDimOf (red blue complement : Finset V) :
    Edge coarseGraph → ℕ :=
  fun f => Fintype.card (CrossingConfig (G := G) A
    (![red, blue, complement] f.1.1) (![red, blue, complement] f.1.2))

/-- The canonical coarse bond dimensions are positive under positive bond
dimensions: a crossing configuration always exists (assign the zero index on every
crossing edge). -/
theorem coarseBondDimOf_pos (red blue complement : Finset V)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e) (f : Edge coarseGraph) :
    0 < coarseBondDimOf (A := A) red blue complement f :=
  Fintype.card_pos_iff.mpr ⟨fun g => ⟨0, hpos g.1⟩⟩

/-- The canonical bond model on a super-edge: the fintype enumeration of the
crossing configurations between the two incident regions. -/
noncomputable def bondModelOf (red blue complement : Finset V) (f : Edge coarseGraph) :
    Fin (coarseBondDimOf (A := A) red blue complement f) ≃
      CrossingConfig (G := G) A
        (![red, blue, complement] f.1.1) (![red, blue, complement] f.1.2) :=
  (Fintype.equivFin _).symm

/-! ### The coarse blocking frame of a partition

The three regions, their blocked-tensor injectivities, the partition geometry, and
the canonical bond dimensions assemble a `CoarseBlockingFrame`.  Its leg
identifications are built from the two bond models on each super-site's incident
super-edges through the region-level boundary-edge split of the region. -/

/-- The coarse blocking frame of three partitioned, blocked-injective regions, with
the canonical bond dimensions and the leg identifications assembled from the bond
models through the boundary-edge split of each region.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def coarseFrameOfRegions
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    CoarseBlockingFrame (G := G) (d := d) A where
  red := red
  blue := blue
  complement := complement
  red_injective := hRed
  blue_injective := hBlue
  complement_injective := hCompl
  pos_dim := hd
  coarseBondDim := coarseBondDimOf red blue complement
  pos_coarseBondDim := fun f => coarseBondDimOf_pos red blue complement hpos f
  legEquivRed :=
    (legPair0.trans
      ((bondModelOf red blue complement coarseEdgeRB).prodCongr
        (bondModelOf red blue complement coarseEdgeRC))).trans
      (redBoundaryEquivOf hrb hrc hbc hcover).symm
  legEquivBlue :=
    (legPair1.trans
      ((bondModelOf red blue complement coarseEdgeRB).prodCongr
        (bondModelOf red blue complement coarseEdgeBC))).trans
      (blueBoundaryEquivOf hrb hrc hbc hcover).symm
  legEquivComplement :=
    (legPair2.trans
      ((bondModelOf red blue complement coarseEdgeRC).prodCongr
        (bondModelOf red blue complement coarseEdgeBC))).trans
      (complementBoundaryEquivOf hrb hrc hbc hcover).symm

@[simp] theorem coarseFrameOfRegions_red
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).red = red := rfl

@[simp] theorem coarseFrameOfRegions_blue
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).blue = blue := rfl

@[simp] theorem coarseFrameOfRegions_complement
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).complement =
      complement := rfl

@[simp] theorem coarseFrameOfRegions_coarseBondDim
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).coarseBondDim =
      coarseBondDimOf (A := A) red blue complement := rfl

/-! ### The coherent coarse blocking frame

A coherent coarse blocking frame extends the coarse blocking frame above with the
per-super-edge bond models and the six factoring fields.  The bond models are the
canonical fintype enumerations supplied per super-edge by a case split; the
factoring fields then hold because each leg identification is, by construction, the
boundary split read through the bond model on the corresponding incident
super-edge. -/

/-- The canonical bond model of the coarse blocking frame, supplied per super-edge
by a case split on the three super-edges. -/
noncomputable def coherentBondModel
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) (f : Edge coarseGraph) :
    Fin ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).coarseBondDim f) ≃
      CrossingConfig (G := G) A
        ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).edgeRegions f).1
        ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).edgeRegions f).2 :=
  if h : f = coarseEdgeRB then h ▸ bondModelOf red blue complement coarseEdgeRB
  else if h2 : f = coarseEdgeRC then h2 ▸ bondModelOf red blue complement coarseEdgeRC
  else if h3 : f = coarseEdgeBC then h3 ▸ bondModelOf red blue complement coarseEdgeBC
  else absurd ((coarse_edge_cases f).resolve_left h |>.resolve_left h2) h3

theorem coherentBondModel_rb
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeRB =
      bondModelOf red blue complement coarseEdgeRB := by
  rw [coherentBondModel, dif_pos rfl]

theorem coherentBondModel_rc
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeRC =
      bondModelOf red blue complement coarseEdgeRC := by
  rw [coherentBondModel, dif_neg (by decide), dif_pos rfl]

theorem coherentBondModel_bc
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeBC =
      bondModelOf red blue complement coarseEdgeBC := by
  rw [coherentBondModel, dif_neg (by decide), dif_neg (by decide), dif_pos rfl]

/-! ### The six factoring fields

Each factoring field is proved as a standalone lemma so the coherent-frame
constructor reduces to assembling the proved pieces.  The proof of each is the same:
identify the named incident super-edge, reduce the bond model through
`coherentBondModel_*`, unfold the leg identification to the boundary split read
through the bond model, and collapse the dichotomy by the crossing classification. -/

section Factoring
variable
  (hRed : RegionBlockedTensorInjective (G := G) A red)
  (hBlue : RegionBlockedTensorInjective (G := G) A blue)
  (hCompl : RegionBlockedTensorInjective (G := G) A complement)
  (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
  (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
  (hcover : red ∪ blue ∪ complement = Finset.univ)

/-- The red super-site reads its `r-b` boundary edges through the `r-b` bond model. -/
theorem coarseFrameOfRegions_factor_red
    (legs : (ie : IncidentEdge coarseGraph 0) →
      Fin ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).coarseBondDim ie.1))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G)
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).red b})
    (hf : IsCrossingEdge (G := G) A
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).red
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).blue b.1)
    (ie : IncidentEdge coarseGraph 0) (hie : ie.1 = coarseEdgeRB) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).legEquivRed legs b =
      (coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeRB
        (hie ▸ legs ie) ⟨b.1, hf⟩ : Fin (A.bondDim b.1)) := by
  have hieEq : ie = incidentRB0 := Subtype.ext hie
  subst hieEq
  rw [coherentBondModel_rb]
  change ((redBoundaryEquivOf (A := A) hrb hrc hbc hcover).symm
    (legPair0.trans
      ((bondModelOf red blue complement coarseEdgeRB).prodCongr
        (bondModelOf red blue complement coarseEdgeRC)) legs)) b = _
  rw [redBoundaryEquivOf, Equiv.coe_fn_symm_mk,
    dif_pos (show IsCrossingEdge (G := G) A red blue b.1 from hf)]
  rfl

/-- The red super-site reads its `r-c` boundary edges through the `r-c` bond model. -/
theorem coarseFrameOfRegions_factor_red_rc
    (legs : (ie : IncidentEdge coarseGraph 0) →
      Fin ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).coarseBondDim ie.1))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G)
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).red b})
    (hf : IsCrossingEdge (G := G) A
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).red
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).complement b.1)
    (ie : IncidentEdge coarseGraph 0) (hie : ie.1 = coarseEdgeRC) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).legEquivRed legs b =
      (coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeRC
        (hie ▸ legs ie) ⟨b.1, hf⟩ : Fin (A.bondDim b.1)) := by
  have hieEq : ie = incidentRC0 := Subtype.ext hie
  subst hieEq
  rw [coherentBondModel_rc]
  change ((redBoundaryEquivOf (A := A) hrb hrc hbc hcover).symm
    (legPair0.trans
      ((bondModelOf red blue complement coarseEdgeRB).prodCongr
        (bondModelOf red blue complement coarseEdgeRC)) legs)) b = _
  rw [redBoundaryEquivOf, Equiv.coe_fn_symm_mk,
    dif_neg (show ¬ IsCrossingEdge (G := G) A red blue b.1 from
      fun h => not_crossing_red_blue_red_complement hrb hrc hbc h hf)]
  rfl

/-- The blue super-site reads its `r-b` boundary edges through the `r-b` bond model. -/
theorem coarseFrameOfRegions_factor_blue_rb
    (legs : (ie : IncidentEdge coarseGraph 1) →
      Fin ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).coarseBondDim ie.1))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G)
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).blue b})
    (hf : IsCrossingEdge (G := G) A
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).red
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).blue b.1)
    (ie : IncidentEdge coarseGraph 1) (hie : ie.1 = coarseEdgeRB) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).legEquivBlue legs b =
      (coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeRB
        (hie ▸ legs ie) ⟨b.1, hf⟩ : Fin (A.bondDim b.1)) := by
  have hieEq : ie = incidentRB1 := Subtype.ext hie
  subst hieEq
  rw [coherentBondModel_rb]
  change ((blueBoundaryEquivOf (A := A) hrb hrc hbc hcover).symm
    (legPair1.trans
      ((bondModelOf red blue complement coarseEdgeRB).prodCongr
        (bondModelOf red blue complement coarseEdgeBC)) legs)) b = _
  rw [blueBoundaryEquivOf, Equiv.coe_fn_symm_mk,
    dif_pos (show IsCrossingEdge (G := G) A red blue b.1 from hf)]
  rfl

/-- The blue super-site reads its `b-c` boundary edges through the `b-c` bond model. -/
theorem coarseFrameOfRegions_factor_blue_bc
    (legs : (ie : IncidentEdge coarseGraph 1) →
      Fin ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).coarseBondDim ie.1))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G)
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).blue b})
    (hf : IsCrossingEdge (G := G) A
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).blue
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).complement b.1)
    (ie : IncidentEdge coarseGraph 1) (hie : ie.1 = coarseEdgeBC) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).legEquivBlue legs b =
      (coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeBC
        (hie ▸ legs ie) ⟨b.1, hf⟩ : Fin (A.bondDim b.1)) := by
  have hieEq : ie = incidentBC1 := Subtype.ext hie
  subst hieEq
  rw [coherentBondModel_bc]
  change ((blueBoundaryEquivOf (A := A) hrb hrc hbc hcover).symm
    (legPair1.trans
      ((bondModelOf red blue complement coarseEdgeRB).prodCongr
        (bondModelOf red blue complement coarseEdgeBC)) legs)) b = _
  rw [blueBoundaryEquivOf, Equiv.coe_fn_symm_mk,
    dif_neg (show ¬ IsCrossingEdge (G := G) A red blue b.1 from
      fun h => not_crossing_red_blue_blue_complement hrb hrc hbc h hf)]
  rfl

/-- The complement super-site reads its `r-c` boundary edges through the `r-c` bond
model. -/
theorem coarseFrameOfRegions_factor_compl_rc
    (legs : (ie : IncidentEdge coarseGraph 2) →
      Fin ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).coarseBondDim ie.1))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G)
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).complement b})
    (hf : IsCrossingEdge (G := G) A
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).red
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).complement b.1)
    (ie : IncidentEdge coarseGraph 2) (hie : ie.1 = coarseEdgeRC) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).legEquivComplement
        legs b =
      (coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeRC
        (hie ▸ legs ie) ⟨b.1, hf⟩ : Fin (A.bondDim b.1)) := by
  have hieEq : ie = incidentRC2 := Subtype.ext hie
  subst hieEq
  rw [coherentBondModel_rc]
  change ((complementBoundaryEquivOf (A := A) hrb hrc hbc hcover).symm
    (legPair2.trans
      ((bondModelOf red blue complement coarseEdgeRC).prodCongr
        (bondModelOf red blue complement coarseEdgeBC)) legs)) b = _
  rw [complementBoundaryEquivOf, Equiv.coe_fn_symm_mk,
    dif_pos (show IsCrossingEdge (G := G) A red complement b.1 from hf)]
  rfl

/-- The complement super-site reads its `b-c` boundary edges through the `b-c` bond
model. -/
theorem coarseFrameOfRegions_factor_compl_bc
    (legs : (ie : IncidentEdge coarseGraph 2) →
      Fin ((coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).coarseBondDim ie.1))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G)
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).complement b})
    (hf : IsCrossingEdge (G := G) A
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).blue
      (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).complement b.1)
    (ie : IncidentEdge coarseGraph 2) (hie : ie.1 = coarseEdgeBC) :
    (coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).legEquivComplement
        legs b =
      (coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover coarseEdgeBC
        (hie ▸ legs ie) ⟨b.1, hf⟩ : Fin (A.bondDim b.1)) := by
  have hieEq : ie = incidentBC2 := Subtype.ext hie
  subst hieEq
  rw [coherentBondModel_bc]
  change ((complementBoundaryEquivOf (A := A) hrb hrc hbc hcover).symm
    (legPair2.trans
      ((bondModelOf red blue complement coarseEdgeRC).prodCongr
        (bondModelOf red blue complement coarseEdgeBC)) legs)) b = _
  rw [complementBoundaryEquivOf, Equiv.coe_fn_symm_mk,
    dif_neg (show ¬ IsCrossingEdge (G := G) A red complement b.1 from
      fun h => not_crossing_red_complement_blue_complement hrb hrc hbc h hf)]
  rfl

end Factoring

/-- **The coherent coarse blocking frame of three partitioned, blocked-injective
regions.**

The underlying coarse blocking frame is `coarseFrameOfRegions`; the bond models are
the canonical per-super-edge enumerations `coherentBondModel`.  Each factoring field
is the corresponding standalone lemma: the leg identification reads each boundary
edge through the bond model on its incident super-edge.

This is the frame consumed by the per-edge gauge interface
`exists_regionEdgeGauge_of_coherentFrames`.  No single-vertex injectivity of the
original tensor is used: the only injectivity inputs are the three blocked-region
injectivities `hRed`, `hBlue`, `hCompl`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def coherentFrameOfRegions
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    CoherentCoarseBlockingFrame (G := G) (d := d) A where
  toCoarseBlockingFrame := coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover
  bondModel := coherentBondModel hRed hBlue hCompl hd hpos hrb hrc hbc hcover
  factor_red := coarseFrameOfRegions_factor_red hRed hBlue hCompl hd hpos hrb hrc hbc hcover
  factor_red_rc := coarseFrameOfRegions_factor_red_rc hRed hBlue hCompl hd hpos hrb hrc hbc hcover
  factor_blue_rb := coarseFrameOfRegions_factor_blue_rb hRed hBlue hCompl hd hpos hrb hrc hbc hcover
  factor_blue_bc := coarseFrameOfRegions_factor_blue_bc hRed hBlue hCompl hd hpos hrb hrc hbc hcover
  factor_compl_rc :=
    coarseFrameOfRegions_factor_compl_rc hRed hBlue hCompl hd hpos hrb hrc hbc hcover
  factor_compl_bc :=
    coarseFrameOfRegions_factor_compl_bc hRed hBlue hCompl hd hpos hrb hrc hbc hcover

@[simp] theorem coherentFrameOfRegions_frame
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coherentFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).toCoarseBlockingFrame =
      coarseFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover := rfl

@[simp] theorem coherentFrameOfRegions_red
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coherentFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).frame.red = red := rfl

@[simp] theorem coherentFrameOfRegions_blue
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coherentFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).frame.blue = blue := rfl

@[simp] theorem coherentFrameOfRegions_complement
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coherentFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).frame.complement =
      complement := rfl

/-- The coherent frame of three partitioned regions is partitioned. -/
theorem coherentFrameOfRegions_isPartition
    (hRed : RegionBlockedTensorInjective (G := G) A red)
    (hBlue : RegionBlockedTensorInjective (G := G) A blue)
    (hCompl : RegionBlockedTensorInjective (G := G) A complement)
    (hd : 0 < d) (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hrb : Disjoint red blue) (hrc : Disjoint red complement) (hbc : Disjoint blue complement)
    (hcover : red ∪ blue ∪ complement = Finset.univ) :
    (coherentFrameOfRegions hRed hBlue hCompl hd hpos hrb hrc hbc hcover).frame.IsPartition :=
  ⟨hrb, hrc, hbc, hcover⟩

end PEPS
end TNLean
