/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameChanges.DyadicDirectRepaintingRewrite
import TNLean.PEPS.Approximation.FrameChanges.GuideFrameRewriteCircuit
import TNLean.PEPS.Approximation.Guides.DyadicReadingFootprints

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

## The resize of a hole as one gate

Combining the plane conditions of the resize of one hole (`exists_resize_planeConditions`) with
the small-patch rewrite between frames of guides as one gate
(`GuideFrameRewrite.PlaneConditions.exists_originalCircuit`): the resize of the hole at a grid
corner `c₀`, from the frame of the reading `g` with hole patches `holeOld` at `V` to the frame of
the same reading with hole patches `holeNew`, is an original circuit with at most one nonprivate
gate whose participants are parties of the labels of the nine blocks around the block below and
to the left of `c₀`, with reference-vector error at most `(2b + 1) L^{-20}` (`resize_step`).

### Main results

* `Approximation.resize_step_isSourceBounded`, `Approximation.resize_step`: with and without
  the bound of `2b` pair sources in every monomial.

### References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`, lines 529–541 and
  574–583; Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218.

## The resizes of a level with one footprint ratio

On entering level `n`, the protocol of Proposition 7.1 resizes the main holes of a reading of a
guide uniform on the `2n`-blocks from the radius `h_{2n}` to the radius `h_n`, one hole at a time
(`06-geometry.tex`, lines 529–541). Every ratio `ν ≤ resizeRatio ε₀ = min(ε₀, 1) / 8` gives the
two-owner condition of these readings, at every intermediate configuration
(`resizing_footprintRatio_mixed_reading_of_le`), in place of the minimum given by the compactness
observation. For every such ratio `ν > 0` this file takes the patches of radius `u = ν n`, so
that `2 u = ν (2 n)`, and every `b` bounding the number of net patches, and so turns every such
resize into one gate (`resize_step_reading_of_le`), with the two-owner hypotheses of
`resize_step` discharged.

### Main results

* `Approximation.resize_step_reading_isSourceBounded_of_le`,
  `Approximation.resize_step_reading_of_le`: with and without the bound of `2b` pair sources in
  every monomial.

### References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the hole radii (lines
  102–133), the compactness observation (lines 447–479), the hole resizing (lines 529–541) and the
  order of the constants (lines 559–570).
-/

section

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
end

end

section

open Set Metric

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame TNLean.Lattice.Sheet TNLean.Lattice.PartyCircuit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

/-- **The resize of a hole as one gate, with its pair sources.** The conclusion of `resize_step`,
together with the bound of `2b` pair sources in every monomial of the gate.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 529–541 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218; Theorem 5.2, item 3, `04-compression.tex`,
lines 143–147. -/
theorem resize_step_isSourceBounded [NeZero q] {N R u : ℝ} (hN : 0 < N) (hR : 0 < R)
    (hu : 0 < u) (hsep : 4 * R + 3 * u < N) {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ} {v : ℝ × ℝ}
    {g : ℝ × ℝ → κ}
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
          ball c (holeNew c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃)
    (hpOld : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (holeOld z).outer (holeOld z').outer)
    (hpNew : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (holeNew z).outer (holeNew z').outer)
    {C c b L : ℕ} (hL : 1 ≤ L) (hcardOld : ∀ z, Fintype.card (holeOld z).Tag ≤ C * L ^ c)
    (hcardNew : ∀ z, Fintype.card (holeNew z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    (hb : (2 * (2 * R + u) / u + 1) ^ 2 ≤ b) (hb9 : 9 ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (holeOld z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (holeOld z).Tag) :
    ∃ P : Finset Party, P.card ≤ 9 ∧
      (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + (Q.1 - 1, Q.2 - 1)))) ∧
      ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V holeOld hpOld).regs
        (guideFrame pos q g own ph rank V holeNew hpNew).regs,
      w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g own ph rank V holeOld hpOld).regIso.symm
          ((guideFrame pos q g own ph rank V holeOld hpOld).refVec Ω)) -
        (guideFrame pos q g own ph rank V holeNew hpNew).regIso.symm
          ((guideFrame pos q g own ph rank V holeNew hpNew).refVec Ω)‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * b) := by
  obtain ⟨G, hG, ho, hn', how, hph, hrk, hho, hhn, hpt, hUA, hUA', hA, hA', hN', hP, hP₀,
    hdesc⟩ := exists_resize_planeConditions (Party := Party) hN hR hu hsep hg own ph rank hV hc₀
      hVc holeOld holeNew patch hcenter hscale hsame hpatch htwoOld htwoNew
  subst ho how hph hrk hho hhn hpt
  obtain ⟨w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hG.exists_originalCircuit_isSourceBounded (C := C)
    (c := c) (b := b) hL
    (fun a _ => hcardNew a) (fun z _ => hcardPatch z) (fun a _ => hcardOld a)
    (by exact_mod_cast hN'.trans hb) (hA.trans (by omega)) (hA'.trans (by omega))
    (hP.trans hb9) hΩ (fun z _ => hεpatch z) (fun a _ => hεhole a) hP₀ (fun z _ => htag z)
  have e₂ : G.newFrame = guideFrame pos q G.old G.own G.ph G.rank V G.holeNew hpNew := by
    rw [G.newFrame_eq hUA' hpNew, hn']
  rw [← G.oldFrame_eq hUA hpOld, ← e₂]
  exact ⟨G.parties, hP, hdesc, w, h₁, h₂, h₃, h₄, h₅, h₆⟩

/-- **The resize of a hole as one gate.** In the setting of `exists_resize_planeConditions`,
suppose moreover that every hole patch of the two frames and every patch has at most `C L^c`
cylinder terms, that every patch and every old hole patch has error at most `L^{-60}` on `Ω`, with
`‖Ω‖ ≤ 1`, that every old hole patch has a tag, and that `b` is at least `9` and the number
`(2 (2 R + u) / u + 1)²` of net patches. There is a set of at most `9` parties, those of the
labels of the nine blocks around the block `Q - (1, 1)`, and an original circuit from the
registers of the frame of `g` with hole patches `holeOld` at `V` to those of the frame of `g` with
hole patches `holeNew` at `V`, with at most one nonprivate gate, all participants in that set,
expansion bounds as in `GuideFrameRewrite.PlaneConditions.exists_originalCircuit`, and
reference-vector error at most `(2b + 1) L^{-20}`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 529–541 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218. -/
theorem resize_step [NeZero q] {N R u : ℝ} (hN : 0 < N) (hR : 0 < R) (hu : 0 < u)
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
          ball c (holeNew c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃)
    (hpOld : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (holeOld z).outer (holeOld z').outer)
    (hpNew : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (holeNew z).outer (holeNew z').outer)
    {C c b L : ℕ} (hL : 1 ≤ L) (hcardOld : ∀ z, Fintype.card (holeOld z).Tag ≤ C * L ^ c)
    (hcardNew : ∀ z, Fintype.card (holeNew z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    (hb : (2 * (2 * R + u) / u + 1) ^ 2 ≤ b) (hb9 : 9 ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (holeOld z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (holeOld z).Tag) :
    ∃ P : Finset Party, P.card ≤ 9 ∧
      (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + (Q.1 - 1, Q.2 - 1)))) ∧
      ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V holeOld hpOld).regs
        (guideFrame pos q g own ph rank V holeNew hpNew).regs,
      w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g own ph rank V holeOld hpOld).regIso.symm
          ((guideFrame pos q g own ph rank V holeOld hpOld).refVec Ω)) -
        (guideFrame pos q g own ph rank V holeNew hpNew).regIso.symm
          ((guideFrame pos q g own ph rank V holeNew hpNew).refVec Ω)‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  obtain ⟨P, h₁, h₂, w, h₃, h₄, h₅, h₆, h₇, -⟩ := resize_step_isSourceBounded hN hR hu hsep hg own
    ph rank hV hc₀ hVc holeOld holeNew patch hcenter hscale hsame hpatch htwoOld htwoNew hpOld hpNew
    hL hcardOld hcardNew hcardPatch hb hb9 hΩ hεpatch hεhole htag
  exact ⟨P, h₁, h₂, w, h₃, h₄, h₅, h₆, h₇⟩

end TNLean.PEPS.Approximation
end

end

section

open Set Metric

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame TNLean.Lattice.Sheet TNLean.Lattice.PartyCircuit

/-- **The resizes of a level as gates, with one footprint ratio and their pair sources.** The
conclusion of `resize_step_reading_of_le`, together with the bound of `2b` pair sources in every
monomial of each gate.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 102–133, 447–479, 529–541 and 559–570;
Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
theorem resize_step_reading_isSourceBounded_of_le {ε₀ : ℝ} (hε : 0 < ε₀)
    (hε₀ : ε₀ ≤ 1 / 16) :
    ∀ ν : ℝ, 0 < ν → ν ≤ resizeRatio ε₀ → ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
      {κ Party : Type} {n t : ℝ}, 0 < n → n < t → ∀ {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ}
      {g : ℝ × ℝ → κ}, IsDisplacedReading g (blockGuide (2 * n) lab) v → ∀ (own : κ → Party)
      (ph : κ) (rank : κ → ℕ) {V : Finset (ℝ × ℝ)}, (∀ c ∈ V, IsTrueVertex g c) →
      blockCorner (2 * n) Q ∈ V →
      (∀ c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)), IsTrueVertex g c → c ∈ V) →
      ∀ (holeOld holeNew patch : ℝ × ℝ → SquarePatch pos q),
      (∀ z, (holeOld z).center = z ∧ (holeNew z).center = z) →
      (∀ z, ((holeOld z).scale = holeRadius ε₀ n t ∨
          (holeOld z).scale = holeRadius ε₀ (2 * n) t) ∧
        ((holeNew z).scale = holeRadius ε₀ n t ∨
          (holeNew z).scale = holeRadius ε₀ (2 * n) t)) →
      (∀ z, z ≠ blockCorner (2 * n) Q → holeOld z = holeNew z) →
      (∀ z, (patch z).center = z ∧ (patch z).scale = ν * n) →
      ∀ (hpOld : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (holeOld z).outer (holeOld z').outer)
        (hpNew : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (holeNew z).outer (holeNew z').outer)
        {C c b L : ℕ}, 1 ≤ L → (∀ z, Fintype.card (holeOld z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (holeNew z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c) →
      (2 * (4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (b : ℝ) → 9 ≤ b →
      ∀ {Ω : EuclideanSpace ℂ (ι → Fin q)}, ‖Ω‖ ≤ 1 →
      (∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, ‖act (holeOld z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, Nonempty (holeOld z).Tag) →
      ∃ P : Finset Party, P.card ≤ 9 ∧
        (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + (Q.1 - 1, Q.2 - 1)))) ∧
        ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V holeOld hpOld).regs
          (guideFrame pos q g own ph rank V holeNew hpNew).regs,
        w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
        w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) *
          (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
            L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
        w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
          L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
        ‖w.eval ((guideFrame pos q g own ph rank V holeOld hpOld).regIso.symm
            ((guideFrame pos q g own ph rank V holeOld hpOld).refVec Ω)) -
          (guideFrame pos q g own ph rank V holeNew hpNew).regIso.symm
            ((guideFrame pos q g own ph rank V holeNew hpNew).refVec Ω)‖ ≤
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
        w.IsSourceBounded (2 * b) := by
  refine fun ν hν hνν' {v} _ {ι _ _ q _ pos κ Party n t} hn hnt {lab Q g} hg own ph rank
    {V} hV hc₀ hVc holeOld holeNew patch hcenter hscale hsame hpatch hpOld hpNew
    {C c b L} hL hcOld hcNew hcPatch hb hb9 {Ω} hΩ hεp hεh htag => ?_
  have hνle : ν ≤ 1 / 4 := (hνν'.trans (resizeRatio_le ε₀)).trans (by norm_num)
  have hn2 : 0 < 2 * n := by positivity
  have hRle : ∀ r, r = holeRadius ε₀ n t ∨ r = holeRadius ε₀ (2 * n) t → r ≤ 2 * ε₀ * n := by
    rintro r (rfl | rfl) <;> simp only [holeRadius]
    · nlinarith [min_le_left n t]
    · nlinarith [min_le_left (2 * n) t]
  have htwo : ∀ hole : ℝ × ℝ → SquarePatch pos q, (∀ z, (hole z).scale = holeRadius ε₀ n t ∨
      (hole z).scale = holeRadius ε₀ (2 * n) t) →
      ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        p ∈ (closedBall x (2 * (ν * n)) ∩ closedBall (blockCorner (2 * n) Q) (2 * n)) \
          ⋃ c ∈ {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)) ∧ IsTrueVertex g c},
            ball c (hole c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃ := by
    intro hole hs x p₁ p₂ p₃ hp
    refine resizing_footprintRatio_mixed_reading_of_le hε hνν' hn hnt lab Q g hg
      (fun c => (hole c).scale) hs x p₁ p₂ p₃ fun p hp' => ?_
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp p hp'
    refine ⟨⟨closedBall_subset_closedBall ?_ h1, by rwa [mul_one]⟩, by rwa [one_add_one_eq_two,
      mul_comm (2 * n) 2]⟩
    nlinarith
  have hb' : (2 * (2 * (2 * ε₀ * n) + ν * n) / (ν * n) + 1) ^ 2 ≤ (b : ℝ) := by
    have e : 2 * (2 * (2 * ε₀ * n) + ν * n) / (ν * n) = 2 * (4 * ε₀ + ν) / ν := by
      field_simp
      ring
    rwa [e]
  exact resize_step_isSourceBounded (R := 2 * ε₀ * n) hn2 (by positivity) (by positivity)
    (by nlinarith) hg own ph rank hV hc₀ hVc holeOld holeNew patch hcenter
    (fun z => ⟨hRle _ (hscale z).1, hRle _ (hscale z).2⟩) hsame hpatch
    (htwo holeOld fun z => (hscale z).1) (htwo holeNew fun z => (hscale z).2) hpOld hpNew hL
    hcOld hcNew hcPatch hb' hb9 hΩ hεp hεh htag

/-- **The resizes of a level as gates, with one footprint ratio.** Fix `0 < ε₀ ≤ 1/16`. For every
ratio `0 < ν ≤ resizeRatio ε₀ = min(ε₀, 1) / 8`, every generic displacement `v`, every
`0 < n < t` and every reading `g` along `v` of a guide uniform on the `2n`-blocks, the resize
of the hole at a grid corner `c₀` of the `2n`-grid, between hole patches centered at their points
of radii `h_n` or `h_{2n}` that agree away from `c₀`, with patches of radius `ν n`, is a circuit as
in `resize_step` for every `b ≥ 9` with `(2 (4 ε₀ + ν) / ν + 1)² ≤ b`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 102–133, 447–479, 529–541 and 559–570. -/
theorem resize_step_reading_of_le {ε₀ : ℝ} (hε : 0 < ε₀) (hε₀ : ε₀ ≤ 1 / 16) :
    ∀ ν : ℝ, 0 < ν → ν ≤ resizeRatio ε₀ → ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
      {κ Party : Type} {n t : ℝ}, 0 < n → n < t → ∀ {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ}
      {g : ℝ × ℝ → κ}, IsDisplacedReading g (blockGuide (2 * n) lab) v → ∀ (own : κ → Party)
      (ph : κ) (rank : κ → ℕ) {V : Finset (ℝ × ℝ)}, (∀ c ∈ V, IsTrueVertex g c) →
      blockCorner (2 * n) Q ∈ V →
      (∀ c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)), IsTrueVertex g c → c ∈ V) →
      ∀ (holeOld holeNew patch : ℝ × ℝ → SquarePatch pos q),
      (∀ z, (holeOld z).center = z ∧ (holeNew z).center = z) →
      (∀ z, ((holeOld z).scale = holeRadius ε₀ n t ∨
          (holeOld z).scale = holeRadius ε₀ (2 * n) t) ∧
        ((holeNew z).scale = holeRadius ε₀ n t ∨
          (holeNew z).scale = holeRadius ε₀ (2 * n) t)) →
      (∀ z, z ≠ blockCorner (2 * n) Q → holeOld z = holeNew z) →
      (∀ z, (patch z).center = z ∧ (patch z).scale = ν * n) →
      ∀ (hpOld : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (holeOld z).outer (holeOld z').outer)
        (hpNew : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (holeNew z).outer (holeNew z').outer)
        {C c b L : ℕ}, 1 ≤ L → (∀ z, Fintype.card (holeOld z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (holeNew z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c) →
      (2 * (4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (b : ℝ) → 9 ≤ b →
      ∀ {Ω : EuclideanSpace ℂ (ι → Fin q)}, ‖Ω‖ ≤ 1 →
      (∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, ‖act (holeOld z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, Nonempty (holeOld z).Tag) →
      ∃ P : Finset Party, P.card ≤ 9 ∧
        (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + (Q.1 - 1, Q.2 - 1)))) ∧
        ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V holeOld hpOld).regs
          (guideFrame pos q g own ph rank V holeNew hpNew).regs,
        w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
        w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) *
          (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
            L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
        w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
          L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
        ‖w.eval ((guideFrame pos q g own ph rank V holeOld hpOld).regIso.symm
            ((guideFrame pos q g own ph rank V holeOld hpOld).refVec Ω)) -
          (guideFrame pos q g own ph rank V holeNew hpNew).regIso.symm
            ((guideFrame pos q g own ph rank V holeNew hpNew).refVec Ω)‖ ≤
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  refine fun ν hν hνν' {v} hv {ι _ _ q _ pos κ Party n t} hn hnt {lab Q g} hg own ph rank
    {V} hV hc₀ hVc holeOld holeNew patch hcenter hscale hsame hpatch hpOld hpNew
    {C c b L} hL hcOld hcNew hcPatch hb hb9 {Ω} hΩ hεp hεh htag => ?_
  obtain ⟨P, h₁, h₂, w, h₃, h₄, h₅, h₆, h₇, -⟩ :=
    resize_step_reading_isSourceBounded_of_le hε hε₀ ν hν hνν' hv hn hnt hg own ph rank hV hc₀
      hVc holeOld holeNew patch hcenter hscale hsame hpatch hpOld hpNew hL hcOld hcNew hcPatch hb
      hb9 hΩ hεp hεh htag
  exact ⟨P, h₁, h₂, w, h₃, h₄, h₅, h₆, h₇⟩

end TNLean.PEPS.Approximation
end

end
