/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicDirectRepaintingRewrite

/-!
# The resize of a hole as a small-patch rewrite

On entering a level, the protocol of Proposition 7.1 resizes the main holes one at a time, each
by one small-patch rewrite whose patches form a fine net over the two outer footprints of the hole
(`06-geometry.tex`, lines 529–541). This file checks the plane conditions of Lemma 6.3
(`GuideFrameRewrite.PlaneConditions`) for the resize of the hole at a grid corner `c₀` of a guide
uniform on the `N`-blocks, read along a displacement, between frames whose hole patches agree
except at `c₀` and have radii at most `R`, with the two-owner condition of the reading near `c₀`
for the old and the new radii as hypotheses (`exists_resize_planeConditions`). The two-owner
condition is `exists_resizing_footprintRatio_mixed_reading` for `2 u = ν N`.

The guide does not change. The only affected hole, in each frame, is the hole at `c₀`; the
specified parties are the parties of the labels of the four blocks at `c₀` and of their
neighbours.

## Main results

* `Approximation.exists_resize_planeConditions`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the holes and their
  resizing (lines 102–133), the hole resizing by small-patch rewrites (lines 529–541); Lemma 6.3
  `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

open Set Metric Filter Topology

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

/-- A grid corner is the upper right corner of the block below and to its left. -/
theorem blockCorner_mem_closedBlock_sub_one {N : ℝ} (hN : 0 < N) (Q : ℤ × ℤ) :
    blockCorner N Q ∈ closedBlock N (Q.1 - 1, Q.2 - 1) := by
  refine mem_closedSquare.2 ?_
  simp only [blockCorner, Prod.fst_sub, Prod.snd_sub]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **The resize of a hole satisfies the plane conditions of Lemma 6.3.** Let `g` be the reading
along `v` of a guide uniform on the `N`-blocks, `V` a finite set of true vertices of `g`
containing every true vertex within `2 N` of the grid corner `c₀ = blockCorner N Q`, with
`c₀ ∈ V`. Let the hole patches of the two frames be centered at their points, agree away from
`c₀` and have radii at most `R`, and let the patches have radius `u`, with `4 R + 3 u < N`.
Suppose the two-owner condition of `g` for footprints of radius `2 u` in the ball of radius `N`
about `c₀`, outside the open inner holes at the true vertices within `2 N`, for the radii of each
frame. Then there is a rewrite from the frame of `g` with holes at `V` to itself with the resized
hole at `c₀`, with patches on a net over the two outer footprints at `c₀`, satisfying the plane
conditions of Lemma 6.3. It has one affected hole in each frame, at most
`(2 (2 R + u) / u + 1)²` patches, and a nonempty list of at most `9` specified parties, each the
party of the label of a block around `c₀`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 529–541; Lemma 6.3 `lem:small-rewrite`,
`05-frames.tex`, lines 188–207. -/
theorem exists_resize_planeConditions {N R u : ℝ} (hN : 0 < N) (hR : 0 < R) (hu : 0 < u)
    (hsep : 4 * R + 3 * u < N) {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ} {v : ℝ × ℝ} {g : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide N lab) v) (own : κ → Party) (ph : κ)
    (rank : κ → ℕ) {V : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g c)
    (hc₀ : blockCorner N Q ∈ V)
    (hVc : ∀ c ∈ closedBall (blockCorner N Q) (2 * N), IsTrueVertex g c → c ∈ V)
    (holeOld holeNew patch : ℝ × ℝ → SquarePatch pos q)
    (hcenter : ∀ z, (holeOld z).center = z ∧ (holeNew z).center = z)
    (hscale : ∀ z, (holeOld z).scale ≤ R ∧ (holeNew z).scale ≤ R)
    (hsame : ∀ z, z ≠ blockCorner N Q → holeOld z = holeNew z)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (htwoOld : ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
      p ∈ (closedBall x (2 * u) ∩ closedBall (blockCorner N Q) N) \
        ⋃ c ∈ {c | c ∈ closedBall (blockCorner N Q) (2 * N) ∧ IsTrueVertex g c},
          ball c (holeOld c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃)
    (htwoNew : ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
      p ∈ (closedBall x (2 * u) ∩ closedBall (blockCorner N Q) N) \
        ⋃ c ∈ {c | c ∈ closedBall (blockCorner N Q) (2 * N) ∧ IsTrueVertex g c},
          ball c (holeNew c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃) :
    ∃ G : GuideFrameRewrite pos q κ Party, G.PlaneConditions ∧ G.old = g ∧ G.new = g ∧
      G.own = own ∧ G.ph = ph ∧ G.rank = rank ∧ G.holeOld = holeOld ∧ G.holeNew = holeNew ∧
      G.patch = patch ∧ G.untouched ∪ G.oldAffected = V ∧ G.untouched ∪ G.newAffected = V ∧
      G.oldAffected.card ≤ 1 ∧ G.newAffected.card ≤ 1 ∧
      (G.centers.card : ℝ) ≤ (2 * (2 * R + u) / u + 1) ^ 2 ∧ G.parties.card ≤ 9 ∧
      G.parties.Nonempty ∧ ∀ x ∈ G.parties, ∃ R ∈ blockWindow 1,
        x = own (lab (R + (Q.1 - 1, Q.2 - 1))) := by
  classical
  set c₀ := blockCorner N Q
  set S : ℤ × ℤ := (Q.1 - 1, Q.2 - 1)
  have hc₀S : c₀ ∈ closedBlock N S := blockCorner_mem_closedBlock_sub_one hN Q
  set K : Set (ℝ × ℝ) := closedBall c₀ (2 * R)
  obtain ⟨s, hcard, hcov, hnear⟩ := exists_netCover hu (by positivity) (subset_refl K)
  have hbc : ∀ c ∈ V, ∃ Q', c = blockCorner N Q' := fun c hc =>
    (hg.isTrueVertex (hV c hc)).eq_blockCorner hN
  have hfar : ∀ c ∈ V, c ≠ c₀ → N ≤ dist c c₀ := by
    intro c hc hne
    obtain ⟨Q', rfl⟩ := hbc c hc
    exact le_dist_blockCorner_of_ne hN fun h => hne (h ▸ rfl)
  have hpair : ∀ hole : ℝ × ℝ → SquarePatch pos q, (∀ z, (hole z).center = z) →
      (∀ z, (hole z).scale ≤ R) →
      (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer := by
    intro hole hc hs z hz z' hz' hne
    obtain ⟨Q₁, rfl⟩ := hbc z hz
    obtain ⟨Q₂, rfl⟩ := hbc z' hz'
    have hd := le_dist_blockCorner_of_ne hN (fun h : Q₁ = Q₂ => hne (h ▸ rfl))
    refine disjoint_outer_of_disjoint_closedBall ?_
    have h₁ := hs (blockCorner N Q₁)
    have h₂ := hs (blockCorner N Q₂)
    rw [hc, hc]
    exact closedBall_disjoint_closedBall (by linarith)
  set U := V.erase c₀
  have hUA : U ∪ {c₀} = V := by
    ext c
    by_cases hc : c = c₀
    · subst hc; simp [U, hc₀]
    · simp [U, hc]
  have hdU : Disjoint U {c₀} := Finset.disjoint_singleton_right.2 (Finset.notMem_erase c₀ V)
  let G : GuideFrameRewrite pos q κ Party :=
    { old := g, new := g, own := own, ph := ph, rank := rank, untouched := U,
      oldAffected := {c₀}, newAffected := {c₀}, holeOld := holeOld, holeNew := holeNew,
      centers := s.image (blockCorner u), patch := patch,
      parties := ((blockWindow 1).image fun R => lab (R + S)).image own,
      disjoint_untouched_old := hdU, disjoint_untouched_new := hdU
      pairwise_old := by
        rw [hUA]; exact hpair holeOld (fun z => (hcenter z).1) fun z => (hscale z).1
      pairwise_new := by
        rw [hUA]; exact hpair holeNew (fun z => (hcenter z).2) fun z => (hscale z).2 }
  have hnearc : ∀ z ∈ G.centers, ∀ p, dist p (patch z).center ≤ 2 * (patch z).scale →
      dist p c₀ < 3 * u + 2 * R := by
    intro z hz p hp
    obtain ⟨y, hy, hpy⟩ := exists_dist_lt_of_mem_image hpatch hnear z hz p hp
    linarith [dist_triangle p y c₀, mem_closedBall.1 hy]
  have hcover := exists_mem_image_dist_le_scale hpatch hcov
  have hparty : ∀ p, dist p c₀ < N → own (g p) ∈ G.parties := by
    intro p hp
    obtain ⟨R', hR', e⟩ := reading_mem_blockWindow hN hg hc₀S hp
    exact Finset.mem_image.2 ⟨lab (R' + S), Finset.mem_image_of_mem _ hR', e.symm ▸ rfl⟩
  have hU : ∀ c ∈ U, c ∈ V ∧ c ≠ c₀ := fun c hc =>
    ⟨Finset.mem_of_mem_erase hc, Finset.ne_of_mem_erase hc⟩
  have hlabels : ∀ hole : ℝ × ℝ → SquarePatch pos q, (∀ z, (hole z).center = z) →
      (∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        p ∈ (closedBall x (2 * u) ∩ closedBall c₀ N) \
          ⋃ c ∈ {c | c ∈ closedBall c₀ (2 * N) ∧ IsTrueVertex g c},
            ball c (hole c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃) →
      ∀ z ∈ G.centers, ∀ p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        dist p (patch z).center ≤ 2 * (patch z).scale ∧
          ∀ c ∈ V, (hole c).scale ≤ dist p c) →
      g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃ := by
    intro hole hc htw z hz p₁ p₂ p₃ hp
    refine htw z p₁ p₂ p₃ fun p hpm => ?_
    obtain ⟨h1, h2⟩ := hp p hpm
    have hpc := hnearc z hz p h1
    rw [(hpatch z).1, (hpatch z).2] at h1
    refine ⟨⟨mem_closedBall.2 h1, mem_closedBall.2 (by linarith)⟩, ?_⟩
    simp only [mem_iUnion, mem_ball, not_exists, not_lt]
    exact fun c hc' => h2 c (hVc c hc'.1 hc'.2)
  refine ⟨G, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, hUA, hUA, le_of_eq (Finset.card_singleton _), le_of_eq (Finset.card_singleton _), ?_, ?_,
    ?_, ?_⟩
  · intro c hc
    exact ⟨hsame c (hU c hc).2, rfl⟩
  · intro z hz c hc p hp
    have hpc := hnearc z hz p hp
    have hcc := hfar c (hU c hc).1 (hU c hc).2
    change 2 * (holeOld c).scale < dist p (holeOld c).center
    rw [(hcenter c).1]
    linarith [dist_triangle c p c₀, dist_comm p c, (hscale c).1]
  · intro a ha c hc p hp
    obtain rfl := Finset.mem_singleton.1 ha
    have hcc := hfar c (hU c hc).1 (hU c hc).2
    change dist p (holeOld c₀).center ≤ 2 * (holeOld c₀).scale at hp
    change 2 * (holeOld c).scale < dist p (holeOld c).center
    rw [(hcenter c₀).1] at hp
    rw [(hcenter c).1]
    linarith [dist_triangle c p c₀, dist_comm p c, (hscale c).1, (hscale c₀).1]
  · intro a ha c hc p hp
    obtain rfl := Finset.mem_singleton.1 ha
    have hcc := hfar c (hU c hc).1 (hU c hc).2
    change dist p (holeNew c₀).center ≤ 2 * (holeNew c₀).scale at hp
    change 2 * (holeOld c).scale < dist p (holeOld c).center
    rw [(hcenter c₀).2] at hp
    rw [(hcenter c).1]
    linarith [dist_triangle c p c₀, dist_comm p c, (hscale c).1, (hscale c₀).2]
  · intro p hp
    exact absurd rfl hp
  · intro a ha p hp
    obtain rfl := Finset.mem_singleton.1 ha
    change dist p (holeOld c₀).center ≤ 2 * (holeOld c₀).scale at hp
    rw [(hcenter c₀).1] at hp
    exact hcover p (mem_closedBall.2 (by linarith [(hscale c₀).1]))
  · intro a ha p hp
    obtain rfl := Finset.mem_singleton.1 ha
    change dist p (holeNew c₀).center ≤ 2 * (holeNew c₀).scale at hp
    rw [(hcenter c₀).2] at hp
    exact hcover p (mem_closedBall.2 (by linarith [(hscale c₀).2]))
  · intro z hz p₁ h₁ p₂ h₂ p₃ h₃
    refine hlabels holeOld (fun z => (hcenter z).1) htwoOld z hz p₁ p₂ p₃ fun p hp => ?_
    have hp' : p ∈ G.outsideOld z :=
      Set.insert_subset h₁ (Set.insert_subset h₂ (Set.singleton_subset_iff.2 h₃)) hp
    refine ⟨hp'.1, fun c hc => ?_⟩
    have := hp'.2 c (by change c ∈ U ∪ {c₀}; rw [hUA]; exact hc)
    change (holeOld c).scale ≤ dist p (holeOld c).center at this
    rwa [(hcenter c).1] at this
  · intro z hz p₁ h₁ p₂ h₂ p₃ h₃
    refine hlabels holeNew (fun z => (hcenter z).2) htwoNew z hz p₁ p₂ p₃ fun p hp => ?_
    have hp' : p ∈ G.outsideNew z :=
      Set.insert_subset h₁ (Set.insert_subset h₂ (Set.singleton_subset_iff.2 h₃)) hp
    refine ⟨hp'.1, fun c hc => ?_⟩
    have := hp'.2 c (by change c ∈ U ∪ {c₀}; rw [hUA]; exact hc)
    change (holeNew c).scale ≤ dist p (holeNew c).center at this
    rwa [(hcenter c).2] at this
  · rintro p (⟨z, hz, hp⟩ | ⟨a, ha, hp⟩ | ⟨a, ha, hp⟩)
    · have := hnearc z hz p hp
      exact ⟨hparty p (by linarith), hparty p (by linarith)⟩
    · obtain rfl := Finset.mem_singleton.1 ha
      change dist p (holeOld c₀).center ≤ 2 * (holeOld c₀).scale at hp
      rw [(hcenter c₀).1] at hp
      have := (hscale c₀).1
      exact ⟨hparty p (by linarith), hparty p (by linarith)⟩
    · obtain rfl := Finset.mem_singleton.1 ha
      change dist p (holeNew c₀).center ≤ 2 * (holeNew c₀).scale at hp
      rw [(hcenter c₀).2] at hp
      have := (hscale c₀).2
      exact ⟨hparty p (by linarith), hparty p (by linarith)⟩
  · intro a ha
    obtain rfl := Finset.mem_singleton.1 ha
    have hl := (isTagHolder_tagHolder (rank := rank) (ph := ph) (hV c₀ hc₀)).1
    obtain ⟨R', hR', e⟩ := incidentLabel_mem_blockWindow hN hg hc₀S hl
    exact Finset.mem_image.2 ⟨lab (R' + S), Finset.mem_image_of_mem _ hR', congrArg own e.symm⟩
  · intro a ha
    obtain rfl := Finset.mem_singleton.1 ha
    have hl := (isTagHolder_tagHolder (rank := rank) (ph := ph) (hV c₀ hc₀)).1
    obtain ⟨R', hR', e⟩ := incidentLabel_mem_blockWindow hN hg hc₀S hl
    exact Finset.mem_image.2 ⟨lab (R' + S), Finset.mem_image_of_mem _ hR', congrArg own e.symm⟩
  · refine (Nat.cast_le.2 Finset.card_image_le).trans (hcard.trans_eq ?_)
    ring_nf
  · refine Finset.card_image_le.trans (Finset.card_image_le.trans ?_)
    rw [card_blockWindow_one]
  · exact ⟨own (lab (0 + S)), Finset.mem_image_of_mem _
      (Finset.mem_image_of_mem (fun R => lab (R + S)) (by decide))⟩
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.1 hl
    exact ⟨Q', hQ', rfl⟩

end TNLean.PEPS.Approximation
