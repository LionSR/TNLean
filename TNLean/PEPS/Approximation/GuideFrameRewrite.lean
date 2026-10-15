/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicGuideFrames
import TNLean.PEPS.Approximation.PatchRewrite

/-!
# Small-patch rewrites between frames of guides

The changes of the protocol of Proposition 7.1 that are not births, deaths or exchanges (the
direct repaintings of small squares, the hole resizes and the point treatments) are small-patch
rewrites, Lemma 6.3 `lem:small-rewrite`, between encoded frames of guides
(`TNLean.PEPS.Approximation.guideFrame`). This file states the four conditions of Lemma 6.3 for
such a rewrite as conditions in the plane, on the old and the new guide, the holes and the
patches (`GuideFrameRewrite.PlaneConditions`), and derives from them the conditions on the
sampled sites (`GuideFrameRewrite.conditions`).

A rewrite between frames of guides (`GuideFrameRewrite`) has an old and a new guide, read at the
sites through one ownership map `own` from labels to parties, a set of untouched hole centers, the
old and the new affected hole centers, the old and the new hole patches, the centers of the
additional patches with their patches, and the specified list of parties. Its frame form
(`GuideFrameRewrite.toSmallPatchRewrite`) lists the untouched holes first, with the tag holders of
the old guide; condition (v) of `PlaneConditions` asks that the untouched holes, their patches and
their incident labels are the same in the two guides.

The plane conditions:

1. every outer patch square and every affected outer hole square is disjoint from every untouched
   outer hole square;
2. every point at which the owner changes, and every affected outer hole square, is covered by
   the inner patch squares;
3. in every outer patch square, the points outside the open inner holes of the old frame carry at
   most two old labels, and those outside the open inner holes of the new frame at most two new
   labels;
4. the old and new owners on the outer patch squares and on the affected outer hole squares, and
   the affected tag holders, are specified parties.

## Main definitions

* `Approximation.GuideFrameRewrite`, `GuideFrameRewrite.oldFrame`, `GuideFrameRewrite.newFrame`.
* `GuideFrameRewrite.toSmallPatchRewrite`, `GuideFrameRewrite.PlaneConditions`.

## Main results

* `GuideFrameRewrite.conditions`: the plane conditions give the four conditions of Lemma 6.3.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 188–218; the frames of guides, `06-geometry.tex`, lines 69–80 and
  109–125; the point treatments, the direct repaintings and the resizes, lines 481–541.
-/

open Set Metric

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ}

/-- **A rewrite between frames of guides.** The old and new guides with one ownership map, the
placeholder and the ranking that choose the tag holders, the untouched and the affected hole
centers with their patches, the centers of the additional patches with their patches, and the
specified list of parties.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–207, for
the frames of guides of `06-geometry.tex`, lines 69–80 and 109–125. -/
structure GuideFrameRewrite (pos : ι → ℝ × ℝ) (q : ℕ) (κ Party : Type) where
  /-- The guide before the rewrite. -/
  old : ℝ × ℝ → κ
  /-- The guide after the rewrite. -/
  new : ℝ × ℝ → κ
  /-- The party of each label. -/
  own : κ → Party
  /-- The placeholder label, which never holds a tag. -/
  ph : κ
  /-- The ranking choosing the canonical tag holders. -/
  rank : κ → ℕ
  /-- The centers of the untouched holes. -/
  untouched : Finset (ℝ × ℝ)
  /-- The centers of the affected holes of the old frame. -/
  oldAffected : Finset (ℝ × ℝ)
  /-- The centers of the affected holes of the new frame. -/
  newAffected : Finset (ℝ × ℝ)
  /-- The hole patches of the old frame. -/
  holeOld : ℝ × ℝ → SquarePatch pos q
  /-- The hole patches of the new frame. -/
  holeNew : ℝ × ℝ → SquarePatch pos q
  /-- The centers of the additional patches. -/
  centers : Finset (ℝ × ℝ)
  /-- The additional patches. -/
  patch : ℝ × ℝ → SquarePatch pos q
  /-- The specified list of parties. -/
  parties : Finset Party
  disjoint_untouched_old : Disjoint untouched oldAffected
  disjoint_untouched_new : Disjoint untouched newAffected
  pairwise_old : ((untouched ∪ oldAffected : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise
    fun z z' => Disjoint (holeOld z).outer (holeOld z').outer
  pairwise_new : ((untouched ∪ newAffected : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)).Pairwise
    fun z z' => Disjoint (holeNew z).outer (holeNew z').outer

namespace GuideFrameRewrite

variable {κ Party : Type} (G : GuideFrameRewrite pos q κ Party)

/-- The frame of the old guide, with holes at the untouched and the old affected centers. -/
def oldFrame : Frame pos q Party :=
  guideFrame pos q G.old G.own G.ph G.rank (G.untouched ∪ G.oldAffected) G.holeOld G.pairwise_old

/-- The frame of the new guide, with holes at the untouched and the new affected centers. -/
def newFrame : Frame pos q Party :=
  guideFrame pos q G.new G.own G.ph G.rank (G.untouched ∪ G.newAffected) G.holeNew G.pairwise_new

/-- The hole of a guide at a center, with its patch and the party of its canonical tag holder. -/
def holeAt (g : ℝ × ℝ → κ) (hole : ℝ × ℝ → SquarePatch pos q) (z : ℝ × ℝ) :
    Hole pos q Party :=
  ⟨hole z, G.own (tagHolder G.rank g G.ph z)⟩

theorem perm_toList_union {s t : Finset (ℝ × ℝ)} (h : Disjoint s t) :
    (s ∪ t).toList.Perm (s.toList ++ t.toList) := by
  refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) ?_).2 fun z => ?_
  · exact List.nodup_append.2 ⟨Finset.nodup_toList _, Finset.nodup_toList _,
      fun a ha b hb hab => Finset.disjoint_left.1 h (Finset.mem_toList.1 ha)
        (hab ▸ Finset.mem_toList.1 hb)⟩
  · simp

/-- The holes of the old frame, the untouched ones first. -/
theorem perm_oldFrame_holes :
    G.oldFrame.holes.Perm (G.untouched.toList.map (G.holeAt G.old G.holeOld) ++
      G.oldAffected.toList.map (G.holeAt G.old G.holeOld)) := by
  rw [← List.map_append]
  exact (perm_toList_union G.disjoint_untouched_old).map _

/-- The holes of the new frame, the untouched ones first. -/
theorem perm_newFrame_holes :
    G.newFrame.holes.Perm (G.untouched.toList.map (G.holeAt G.new G.holeNew) ++
      G.newAffected.toList.map (G.holeAt G.new G.holeNew)) := by
  rw [← List.map_append]
  exact (perm_toList_union G.disjoint_untouched_new).map _

/-- Condition (v): the untouched holes are the same in the two guides. -/
def UntouchedAgree : Prop :=
  ∀ z ∈ G.untouched, G.holeOld z = G.holeNew z ∧ incidentLabels G.old z = incidentLabels G.new z

theorem map_holeAt_untouched (h : G.UntouchedAgree) :
    G.untouched.toList.map (G.holeAt G.old G.holeOld) =
      G.untouched.toList.map (G.holeAt G.new G.holeNew) :=
  List.map_congr_left fun z hz => by
    obtain ⟨h₁, h₂⟩ := h z (Finset.mem_toList.1 hz)
    simp only [holeAt, h₁, tagHolder_congr (rank := G.rank) (ph := G.ph) h₂]

/-- **The rewrite in frame form.** The untouched holes are listed with the tag holders of the old
guide, followed by the affected holes of each frame. -/
def toSmallPatchRewrite (h : G.UntouchedAgree) : SmallPatchRewrite pos q Party where
  ownerOld x := G.own (G.old (pos x))
  ownerNew x := G.own (G.new (pos x))
  untouched := G.untouched.toList.map (G.holeAt G.old G.holeOld)
  oldAffected := G.oldAffected.toList.map (G.holeAt G.old G.holeOld)
  newAffected := G.newAffected.toList.map (G.holeAt G.new G.holeNew)
  patches := G.centers.toList.map G.patch
  parties := G.parties
  disjoint_old := G.oldFrame.disjoint.perm (G.perm_oldFrame_holes.map _) fun h => Disjoint.symm h
  disjoint_new := by
    rw [G.map_holeAt_untouched h]
    exact G.newFrame.disjoint.perm (G.perm_newFrame_holes.map _) fun h => Disjoint.symm h

/-- The points of the outer square of the patch at `z` outside the open inner holes of the old
frame. -/
def outsideOld (z : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | dist p (G.patch z).center ≤ 2 * (G.patch z).scale ∧
    ∀ c ∈ G.untouched ∪ G.oldAffected, (G.holeOld c).scale ≤ dist p (G.holeOld c).center}

/-- The points of the outer square of the patch at `z` outside the open inner holes of the new
frame. -/
def outsideNew (z : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | dist p (G.patch z).center ≤ 2 * (G.patch z).scale ∧
    ∀ c ∈ G.untouched ∪ G.newAffected, (G.holeNew c).scale ≤ dist p (G.holeNew c).center}

end GuideFrameRewrite

/-- A function on a finite set any three of whose values have a coincidence takes at most two
values. -/
theorem exists_card_le_two_of_three {α β : Type*} (s : Set α) (f : α → β)
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, f a = f b ∨ f a = f c ∨ f b = f c) (t : Finset α) :
    ∃ S : Finset β, S.card ≤ 2 ∧ ∀ a ∈ t, a ∈ s → f a ∈ S := by
  classical
  refine ⟨(t.filter (· ∈ s)).image f, ?_, fun a ha has =>
    Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨ha, has⟩)⟩
  by_contra hlt
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.1 (not_le.1 hlt)
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hz
  rcases h a (Finset.mem_filter.1 ha).2 b (Finset.mem_filter.1 hb).2 c (Finset.mem_filter.1 hc).2
    with h' | h' | h'
  · exact hxy h'
  · exact hxz h'
  · exact hyz h'

theorem mem_outer_iff {P : SquarePatch pos q} {x : ι} :
    x ∈ P.outer ↔ dist (pos x) P.center ≤ 2 * P.scale := by
  simp [SquarePatch.outer, squareSample]

theorem mem_inner_iff {P : SquarePatch pos q} {x : ι} :
    x ∈ P.inner ↔ dist (pos x) P.center ≤ P.scale := by
  simp [SquarePatch.inner, squareSample]

namespace GuideFrameRewrite

variable {κ Party : Type} (G : GuideFrameRewrite pos q κ Party)

/-- **The conditions of Lemma 6.3 in the plane.** The untouched holes agree in the two guides
(v); outer patch squares and affected outer hole squares avoid the untouched outer hole squares
(i); the inner patch squares cover every point whose owner changes and every affected outer hole
square (ii); in each outer patch square the points outside the open inner holes of a frame carry
at most two labels of its guide (iii); the owners on the outer patch squares and on the affected
outer hole squares and the affected tag holders are specified (iv).

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 193–207. -/
structure PlaneConditions : Prop where
  untouched_agree : G.UntouchedAgree
  patch_avoid : ∀ z ∈ G.centers, ∀ c ∈ G.untouched, ∀ p : ℝ × ℝ,
    dist p (G.patch z).center ≤ 2 * (G.patch z).scale →
      2 * (G.holeOld c).scale < dist p (G.holeOld c).center
  oldAffected_avoid : ∀ a ∈ G.oldAffected, ∀ c ∈ G.untouched, ∀ p : ℝ × ℝ,
    dist p (G.holeOld a).center ≤ 2 * (G.holeOld a).scale →
      2 * (G.holeOld c).scale < dist p (G.holeOld c).center
  newAffected_avoid : ∀ a ∈ G.newAffected, ∀ c ∈ G.untouched, ∀ p : ℝ × ℝ,
    dist p (G.holeNew a).center ≤ 2 * (G.holeNew a).scale →
      2 * (G.holeOld c).scale < dist p (G.holeOld c).center
  changed_mem : ∀ p : ℝ × ℝ, G.own (G.old p) ≠ G.own (G.new p) →
    ∃ z ∈ G.centers, dist p (G.patch z).center ≤ (G.patch z).scale
  oldAffected_subset : ∀ a ∈ G.oldAffected, ∀ p : ℝ × ℝ,
    dist p (G.holeOld a).center ≤ 2 * (G.holeOld a).scale →
      ∃ z ∈ G.centers, dist p (G.patch z).center ≤ (G.patch z).scale
  newAffected_subset : ∀ a ∈ G.newAffected, ∀ p : ℝ × ℝ,
    dist p (G.holeNew a).center ≤ 2 * (G.holeNew a).scale →
      ∃ z ∈ G.centers, dist p (G.patch z).center ≤ (G.patch z).scale
  old_labels : ∀ z ∈ G.centers, ∀ p₁ ∈ outsideOld G z, ∀ p₂ ∈ outsideOld G z,
    ∀ p₃ ∈ outsideOld G z, G.old p₁ = G.old p₂ ∨ G.old p₁ = G.old p₃ ∨ G.old p₂ = G.old p₃
  new_labels : ∀ z ∈ G.centers, ∀ p₁ ∈ outsideNew G z, ∀ p₂ ∈ outsideNew G z,
    ∀ p₃ ∈ outsideNew G z, G.new p₁ = G.new p₂ ∨ G.new p₁ = G.new p₃ ∨ G.new p₂ = G.new p₃
  owners_mem : ∀ p : ℝ × ℝ,
    ((∃ z ∈ G.centers, dist p (G.patch z).center ≤ 2 * (G.patch z).scale) ∨
      (∃ a ∈ G.oldAffected, dist p (G.holeOld a).center ≤ 2 * (G.holeOld a).scale) ∨
      (∃ a ∈ G.newAffected, dist p (G.holeNew a).center ≤ 2 * (G.holeNew a).scale)) →
    G.own (G.old p) ∈ G.parties ∧ G.own (G.new p) ∈ G.parties
  oldTag_mem : ∀ a ∈ G.oldAffected, G.own (tagHolder G.rank G.old G.ph a) ∈ G.parties
  newTag_mem : ∀ a ∈ G.newAffected, G.own (tagHolder G.rank G.new G.ph a) ∈ G.parties

variable {G}

private theorem mem_map_holeAt {g : ℝ × ℝ → κ} {hole : ℝ × ℝ → SquarePatch pos q}
    {s : Finset (ℝ × ℝ)} {h : Hole pos q Party} (hh : h ∈ s.toList.map (G.holeAt g hole)) :
    ∃ z ∈ s, h.patch = hole z := by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hh
  exact ⟨z, Finset.mem_toList.1 hz, rfl⟩

private theorem mem_map_holeAt_tag {g : ℝ × ℝ → κ} {hole : ℝ × ℝ → SquarePatch pos q}
    {s : Finset (ℝ × ℝ)} {h : Hole pos q Party} (hh : h ∈ s.toList.map (G.holeAt g hole)) :
    ∃ z ∈ s, h.tagOwner = G.own (tagHolder G.rank g G.ph z) := by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hh
  exact ⟨z, Finset.mem_toList.1 hz, rfl⟩

/-- A site of the footprint of the untouched holes lies in an untouched outer hole square. -/
private theorem exists_of_mem_untouchedFootprint (h : G.UntouchedAgree) {x : ι}
    (hx : x ∈ (G.toSmallPatchRewrite h).untouchedFootprint) :
    ∃ c ∈ G.untouched, dist (pos x) (G.holeOld c).center ≤ 2 * (G.holeOld c).scale := by
  obtain ⟨P, hP, hxP⟩ := hx
  obtain ⟨h', hh', rfl⟩ := List.mem_map.1 hP
  obtain ⟨c, hc, he⟩ := mem_map_holeAt hh'
  exact ⟨c, hc, he ▸ mem_outer_iff.1 hxP⟩

/-- A site outside the inner holes of a frame of the rewrite is outside every open inner hole
of the corresponding guide frame. -/
private theorem le_dist_of_notMem_innerUnion {g : ℝ × ℝ → κ} {hole : ℝ × ℝ → SquarePatch pos q}
    {s t : Finset (ℝ × ℝ)} {x : ι}
    (hx : x ∉ innerUnion ((s.toList.map (G.holeAt g hole) ++ t.toList.map (G.holeAt g hole)).map
      Hole.patch)) :
    ∀ c ∈ s ∪ t, (hole c).scale ≤ dist (pos x) (hole c).center := by
  intro c hc
  by_contra hlt
  refine hx ⟨hole c, List.mem_map.2 ⟨G.holeAt g hole c, ?_, rfl⟩,
    mem_inner_iff.2 (le_of_lt (not_le.1 hlt))⟩
  rcases Finset.mem_union.1 hc with hc | hc
  · exact List.mem_append_left _ (List.mem_map.2 ⟨c, Finset.mem_toList.2 hc, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.2 ⟨c, Finset.mem_toList.2 hc, rfl⟩)

/-- **The plane conditions give the four conditions of Lemma 6.3** on the sampled sites.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 193–207. -/
theorem PlaneConditions.conditions (h : G.PlaneConditions) :
    (G.toSmallPatchRewrite h.untouched_agree).Conditions where
  patch_avoid P hP := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hP
    refine Set.disjoint_left.2 fun x hx hxU => ?_
    obtain ⟨c, hc, hxc⟩ := exists_of_mem_untouchedFootprint h.untouched_agree hxU
    exact (h.patch_avoid z (Finset.mem_toList.1 hz) c hc _ (mem_outer_iff.1 hx)).not_ge hxc
  affected_avoid h' hh' := by
    refine Set.disjoint_left.2 fun x hx hxU => ?_
    obtain ⟨c, hc, hxc⟩ := exists_of_mem_untouchedFootprint h.untouched_agree hxU
    rcases List.mem_append.1 hh' with hh' | hh'
    · obtain ⟨a, ha, he⟩ := mem_map_holeAt hh'
      rw [he] at hx
      exact (h.oldAffected_avoid a ha c hc _ (mem_outer_iff.1 hx)).not_ge hxc
    · obtain ⟨a, ha, he⟩ := mem_map_holeAt hh'
      rw [he] at hx
      exact (h.newAffected_avoid a ha c hc _ (mem_outer_iff.1 hx)).not_ge hxc
  changed_mem x hx := by
    obtain ⟨z, hz, hxz⟩ := h.changed_mem (pos x) hx
    exact ⟨G.patch z, List.mem_map.2 ⟨z, Finset.mem_toList.2 hz, rfl⟩, mem_inner_iff.2 hxz⟩
  affected_subset h' hh' x hx := by
    have key : ∀ p : ℝ × ℝ, (∃ z ∈ G.centers, dist p (G.patch z).center ≤ (G.patch z).scale) →
        p = pos x → x ∈ innerUnion (G.toSmallPatchRewrite h.untouched_agree).patches := by
      rintro p ⟨z, hz, hpz⟩ rfl
      exact ⟨G.patch z, List.mem_map.2 ⟨z, Finset.mem_toList.2 hz, rfl⟩, mem_inner_iff.2 hpz⟩
    rcases List.mem_append.1 hh' with hh' | hh'
    · obtain ⟨a, ha, he⟩ := mem_map_holeAt hh'
      rw [Finset.mem_coe, he] at hx
      exact key _ (h.oldAffected_subset a ha _ (mem_outer_iff.1 hx)) rfl
    · obtain ⟨a, ha, he⟩ := mem_map_holeAt hh'
      rw [Finset.mem_coe, he] at hx
      exact key _ (h.newAffected_subset a ha _ (mem_outer_iff.1 hx)) rfl
  old_owners P hP := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hP
    obtain ⟨S, hS, hSx⟩ := exists_card_le_two_of_three
      {x : ι | pos x ∈ G.outsideOld z} (fun x => G.own (G.old (pos x)))
      (fun a ha b hb c hc => by
        rcases h.old_labels z (Finset.mem_toList.1 hz) _ ha _ hb _ hc with e | e | e <;>
          simp [e]) (G.patch z).outer
    exact ⟨S, hS, fun x hx hxi => hSx x hx ⟨mem_outer_iff.1 hx,
      le_dist_of_notMem_innerUnion (G := G) (g := G.old) hxi⟩⟩
  new_owners P hP := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hP
    obtain ⟨S, hS, hSx⟩ := exists_card_le_two_of_three
      {x : ι | pos x ∈ G.outsideNew z} (fun x => G.own (G.new (pos x)))
      (fun a ha b hb c hc => by
        rcases h.new_labels z (Finset.mem_toList.1 hz) _ ha _ hb _ hc with e | e | e <;>
          simp [e]) (G.patch z).outer
    refine ⟨S, hS, fun x hx hxi => hSx x hx ⟨mem_outer_iff.1 hx, ?_⟩⟩
    have hxi' : x ∉ innerUnion ((G.untouched.toList.map (G.holeAt G.new G.holeNew) ++
        G.newAffected.toList.map (G.holeAt G.new G.holeNew)).map Hole.patch) := by
      have := G.map_holeAt_untouched h.untouched_agree
      simp only [toSmallPatchRewrite, Frame.innerHoles, Frame.patches, this] at hxi
      exact hxi
    exact le_dist_of_notMem_innerUnion (G := G) hxi'
  raw_owners_mem x hx := by
    refine h.owners_mem (pos x) ?_
    rcases hx with ⟨P, hP, hxP⟩ | ⟨P, hP, hxP⟩
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hP
      exact Or.inl ⟨z, Finset.mem_toList.1 hz, mem_outer_iff.1 hxP⟩
    · obtain ⟨h', hh', rfl⟩ := List.mem_map.1 hP
      rcases List.mem_append.1 hh' with hh' | hh'
      · obtain ⟨a, ha, he⟩ := mem_map_holeAt hh'
        exact Or.inr (Or.inl ⟨a, ha, he ▸ mem_outer_iff.1 hxP⟩)
      · obtain ⟨a, ha, he⟩ := mem_map_holeAt hh'
        exact Or.inr (Or.inr ⟨a, ha, he ▸ mem_outer_iff.1 hxP⟩)
  tag_owners_mem h' hh' := by
    rcases List.mem_append.1 hh' with hh' | hh'
    · obtain ⟨a, ha, he⟩ := mem_map_holeAt_tag hh'
      exact he ▸ h.oldTag_mem a ha
    · obtain ⟨a, ha, he⟩ := mem_map_holeAt_tag hh'
      exact he ▸ h.newTag_mem a ha

end GuideFrameRewrite

end TNLean.PEPS.Approximation
