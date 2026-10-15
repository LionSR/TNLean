/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicFootprintScaling
import TNLean.PEPS.Approximation.DyadicSmallPatchCovers
import TNLean.PEPS.Approximation.GuideFrameRewrite

/-!
# Local small-patch rewrites between frames of guides

A point treatment of the protocol of Proposition 7.1 homogenizes a guide on a small square about a
mark and rewrites the frame by one small-patch rewrite whose patches form a fine net over the
treated square and the affected outer holes (`06-geometry.tex`, lines 481–505). This file checks
the plane conditions of Lemma 6.3 (`GuideFrameRewrite.PlaneConditions`) for every such local
rewrite (`exists_local_planeConditions`): the old and the new guide agree outside a closed ball of
radius `ρ₀` about a point `o`; the holes, of radius `r`, are at given finite sets of centers, each
within `ρ₁` of `o` (affected) or at distance at least `ρ₂` from it (untouched), the untouched ones
the same in the two frames; the patches have radius `u`; and

* `max ρ₀ (ρ₁ + 2 r) + 3 u + 4 r < ρ₂`, so the outer patch squares and the affected outer hole
  squares avoid the untouched outer hole squares;
* both guides satisfy the two-owner condition for footprints of radius `2 u` in a set containing
  the ball of radius `max ρ₀ (ρ₁ + 2 r) + 3 u` about `o`, outside open inner holes at centers of
  their frames;
* a given finite list of parties contains the owners within that ball and the affected tag
  holders.

## Main results

* `Approximation.exists_local_planeConditions`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the point treatments and
  their covers (lines 328–339 and 481–505); Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`,
  lines 188–218.
-/

open Set Metric Filter Topology

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

/-- **A local rewrite satisfies the plane conditions of Lemma 6.3.** Let the guides `g` and `g'`
agree at every point at distance more than `ρ₀` from `o`, and let `V`, `V'` be finite sets of
hole centers, with pairwise disjoint outer hole squares, each center within `ρ₁` of `o` or at
distance at least `ρ₂` from it, and the far centers the same in `V` and `V'`. Let the holes have
radius `r`, the patches radius `u`, and `ρ = max ρ₀ (ρ₁ + 2 r)` with `ρ + 3 u + 4 r < ρ₂`.
Suppose that `g` and `g'` satisfy the two-owner condition for footprints of radius `2 u` in a set
`W` containing the ball of radius `ρ + 3 u` about `o`, outside the open inner holes at sets of
centers `H ⊆ V` and `H' ⊆ V'`, and that the list `P` contains the owners in that ball and the
tag holders at the near centers. Then there is a rewrite from the frame of `g` with holes at `V`
to the frame of `g'` with holes at `V'`, with the far holes untouched, the near holes affected,
patches on a net over the ball of radius `ρ` about `o`, and specified parties `P`, satisfying
the plane conditions of Lemma 6.3. It has at most `(2 (ρ + u) / u + 1)²` patches.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 481–505; Lemma 6.3 `lem:small-rewrite`,
`05-frames.tex`, lines 188–207. -/
theorem exists_local_planeConditions {o : ℝ × ℝ} {ρ₀ ρ₁ ρ₂ r u : ℝ} (hr : 0 < r) (hu : 0 < u)
    (hρ₀ : 0 ≤ ρ₀) (hsep : max ρ₀ (ρ₁ + 2 * r) + 3 * u + 4 * r < ρ₂) {g g' : ℝ × ℝ → κ}
    (hchange : ∀ p, ρ₀ < dist p o → g p = g' p) (own : κ → Party) (ph : κ) (rank : κ → ℕ)
    {V V' : Finset (ℝ × ℝ)} (hfar : ∀ c ∈ V, dist c o ≤ ρ₁ ∨ ρ₂ ≤ dist c o)
    (hfar' : ∀ c ∈ V', dist c o ≤ ρ₁ ∨ ρ₂ ≤ dist c o)
    (hVV' : ∀ c, ρ₂ ≤ dist c o → (c ∈ V ↔ c ∈ V')) (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = r)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {W H H' : Set (ℝ × ℝ)} (hW : closedBall o (max ρ₀ (ρ₁ + 2 * r) + 3 * u) ⊆ W)
    (hH : ∀ c ∈ H, c ∈ V) (hH' : ∀ c ∈ H', c ∈ V')
    (htwo : HasTwoOwnerFootprints g W H r (2 * u))
    (htwo' : HasTwoOwnerFootprints g' W H' r (2 * u)) (P : Finset Party)
    (hP : ∀ p, dist p o ≤ max ρ₀ (ρ₁ + 2 * r) + 3 * u → own (g p) ∈ P ∧ own (g' p) ∈ P)
    (hPt : ∀ a ∈ V, dist a o ≤ ρ₁ → own (tagHolder rank g ph a) ∈ P)
    (hPt' : ∀ a ∈ V', dist a o ≤ ρ₁ → own (tagHolder rank g' ph a) ∈ P) :
    ∃ G : GuideFrameRewrite pos q κ Party, G.PlaneConditions ∧ G.old = g ∧ G.new = g' ∧
      G.own = own ∧ G.ph = ph ∧ G.rank = rank ∧ G.holeOld = hole ∧ G.holeNew = hole ∧
      G.patch = patch ∧ G.parties = P ∧ G.untouched ∪ G.oldAffected = V ∧
      G.untouched ∪ G.newAffected = V' ∧ (∀ a ∈ G.oldAffected, dist a o ≤ ρ₁) ∧
      (∀ a ∈ G.newAffected, dist a o ≤ ρ₁) ∧
      (G.centers.card : ℝ) ≤ (2 * (max ρ₀ (ρ₁ + 2 * r) + u) / u + 1) ^ 2 := by
  classical
  set ρ := max ρ₀ (ρ₁ + 2 * r)
  have hρ : 0 ≤ ρ := le_max_of_le_left hρ₀
  set K : Set (ℝ × ℝ) := closedBall o ρ
  obtain ⟨s, hcard, hcov, hnear⟩ := exists_netCover hu hρ (subset_refl K)
  set U := V.filter fun c => ρ₁ < dist c o
  set A := V.filter fun c => dist c o ≤ ρ₁
  set A' := V'.filter fun c => dist c o ≤ ρ₁
  have hUfar : ∀ c ∈ U, c ∈ V ∧ ρ₂ ≤ dist c o := by
    intro c hc
    obtain ⟨hcV, hlt⟩ := Finset.mem_filter.1 hc
    exact ⟨hcV, (hfar c hcV).resolve_left (not_le.2 hlt)⟩
  have hUA : U ∪ A = V := by
    ext c
    by_cases hc : ρ₁ < dist c o
    · simp [U, A, hc, not_le.2 hc]
    · simp [U, A, hc, not_lt.1 hc]
  have hUA' : U ∪ A' = V' := by
    ext c
    by_cases hc : ρ₁ < dist c o
    · simp only [Finset.mem_union, Finset.mem_filter, U, A', hc, not_le.2 hc, and_true,
        and_false, or_false]
      constructor
      · intro hcV
        exact (hVV' c ((hfar c hcV).resolve_left (not_le.2 hc))).1 hcV
      · intro hcV'
        exact (hVV' c ((hfar' c hcV').resolve_left (not_le.2 hc))).2 hcV'
    · simp only [Finset.mem_union, Finset.mem_filter, U, A', hc, not_lt.1 hc, and_true,
        and_false, false_or]
  have hdU : Disjoint U A := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    exact not_le.2 (Finset.mem_filter.1 hc).2 (Finset.mem_filter.1 hc').2
  have hdU' : Disjoint U A' := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    exact not_le.2 (Finset.mem_filter.1 hc).2 (Finset.mem_filter.1 hc').2
  let G : GuideFrameRewrite pos q κ Party :=
    { old := g, new := g', own := own, ph := ph, rank := rank, untouched := U,
      oldAffected := A, newAffected := A', holeOld := hole, holeNew := hole,
      centers := s.image (blockCorner u), patch := patch, parties := P,
      disjoint_untouched_old := hdU, disjoint_untouched_new := hdU'
      pairwise_old := by rw [hUA]; exact hpV
      pairwise_new := by rw [hUA']; exact hpV' }
  have hnearo : ∀ z ∈ G.centers, ∀ p, dist p (patch z).center ≤ 2 * (patch z).scale →
      dist p o < ρ + 3 * u := by
    intro z hz p hp
    obtain ⟨y, hy, hpy⟩ := exists_dist_lt_of_mem_image hpatch hnear z hz p hp
    linarith [dist_triangle p y o, mem_closedBall.1 hy]
  have hcover := exists_mem_image_dist_le_scale hpatch hcov
  have hA : ∀ a ∈ A, a ∈ V ∧ dist a o ≤ ρ₁ := fun a ha => Finset.mem_filter.1 ha
  have hA' : ∀ a ∈ A', a ∈ V' ∧ dist a o ≤ ρ₁ := fun a ha => Finset.mem_filter.1 ha
  have hρ₁ : ρ₁ + 2 * r ≤ ρ := le_max_right _ _
  have hρ₀' : ρ₀ ≤ ρ := le_max_left _ _
  have hlabels : ∀ (g₀ : ℝ × ℝ → κ) (H₀ : Set (ℝ × ℝ)) (V₀ : Finset (ℝ × ℝ)),
      (∀ c ∈ H₀, c ∈ V₀) → HasTwoOwnerFootprints g₀ W H₀ r (2 * u) →
      ∀ z ∈ G.centers, ∀ p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        dist p (patch z).center ≤ 2 * (patch z).scale ∧ ∀ c ∈ V₀, r ≤ dist p c) →
      g₀ p₁ = g₀ p₂ ∨ g₀ p₁ = g₀ p₃ ∨ g₀ p₂ = g₀ p₃ := by
    intro g₀ H₀ V₀ hH₀ htw z hz p₁ p₂ p₃ hp
    have mem : ∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        p ∈ (closedBall z (2 * u) ∩ W) \ ⋃ h ∈ H₀, ball h r := by
      intro p hpm
      obtain ⟨h1, h2⟩ := hp p hpm
      have hpo := hnearo z hz p h1
      rw [(hpatch z).1, (hpatch z).2] at h1
      refine ⟨⟨mem_closedBall.2 h1, hW (mem_closedBall.2 hpo.le)⟩, ?_⟩
      simp only [mem_iUnion, mem_ball, not_exists, not_lt]
      exact fun c hc => h2 c (hH₀ c hc)
    exact htw z p₁ p₂ p₃ (mem p₁ (by simp)) (mem p₂ (by simp)) (mem p₃ (by simp))
  refine ⟨G, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, hUA, hUA', fun a ha => (hA a ha).2, fun a ha => (hA' a ha).2, ?_⟩
  · -- the untouched holes agree
    intro c hc
    refine ⟨rfl, incidentLabels_congr ?_⟩
    have hco := (hUfar c hc).2
    filter_upwards [(isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds
      (show ρ₀ < dist c o by linarith)] with p hp
    exact hchange p hp
  · intro z hz c hc p hp
    have hpo := hnearo z hz p hp
    have hco := (hUfar c hc).2
    rw [(hhole c).1, (hhole c).2]
    linarith [dist_triangle c p o, dist_comm p c]
  · intro a ha c hc p hp
    have hco := (hUfar c hc).2
    rw [(hhole a).1, (hhole a).2] at hp
    rw [(hhole c).1, (hhole c).2]
    linarith [dist_triangle c p o, dist_comm p c, dist_triangle p a o, (hA a ha).2]
  · intro a ha c hc p hp
    have hco := (hUfar c hc).2
    change dist p (hole a).center ≤ 2 * (hole a).scale at hp
    change 2 * (hole c).scale < dist p (hole c).center
    rw [(hhole a).1, (hhole a).2] at hp
    rw [(hhole c).1, (hhole c).2]
    linarith [dist_triangle c p o, dist_comm p c, dist_triangle p a o, (hA' a ha).2]
  · intro p hp
    have hne : g p ≠ g' p := fun e => hp (by change own (g p) = own (g' p); rw [e])
    refine hcover p (mem_closedBall.2 ?_)
    by_contra hlt
    exact hne (hchange p (by linarith))
  · intro a ha p hp
    rw [(hhole a).1, (hhole a).2] at hp
    exact hcover p (mem_closedBall.2 (by linarith [dist_triangle p a o, (hA a ha).2]))
  · intro a ha p hp
    change dist p (hole a).center ≤ 2 * (hole a).scale at hp
    rw [(hhole a).1, (hhole a).2] at hp
    exact hcover p (mem_closedBall.2 (by linarith [dist_triangle p a o, (hA' a ha).2]))
  · intro z hz p₁ h₁ p₂ h₂ p₃ h₃
    refine hlabels g H V hH htwo z hz p₁ p₂ p₃ fun p hp => ?_
    have hp' : p ∈ G.outsideOld z :=
      Set.insert_subset h₁ (Set.insert_subset h₂ (Set.singleton_subset_iff.2 h₃)) hp
    refine ⟨hp'.1, fun c hc => ?_⟩
    have := hp'.2 c (by change c ∈ U ∪ A; rw [hUA]; exact hc)
    rwa [(hhole c).1, (hhole c).2] at this
  · intro z hz p₁ h₁ p₂ h₂ p₃ h₃
    refine hlabels g' H' V' hH' htwo' z hz p₁ p₂ p₃ fun p hp => ?_
    have hp' : p ∈ G.outsideNew z :=
      Set.insert_subset h₁ (Set.insert_subset h₂ (Set.singleton_subset_iff.2 h₃)) hp
    refine ⟨hp'.1, fun c hc => ?_⟩
    have := hp'.2 c (by change c ∈ U ∪ A'; rw [hUA']; exact hc)
    change (hole c).scale ≤ dist p (hole c).center at this
    rwa [(hhole c).1, (hhole c).2] at this
  · rintro p (⟨z, hz, hp⟩ | ⟨a, ha, hp⟩ | ⟨a, ha, hp⟩)
    · exact hP p (hnearo z hz p hp).le
    · rw [(hhole a).1, (hhole a).2] at hp
      exact hP p (by linarith [dist_triangle p a o, (hA a ha).2])
    · change dist p (hole a).center ≤ 2 * (hole a).scale at hp
      rw [(hhole a).1, (hhole a).2] at hp
      exact hP p (by linarith [dist_triangle p a o, (hA' a ha).2])
  · intro a ha
    exact hPt a (hA a ha).1 (hA a ha).2
  · intro a ha
    exact hPt' a (hA' a ha).1 (hA' a ha).2
  · exact (Nat.cast_le.2 Finset.card_image_le).trans hcard

end TNLean.PEPS.Approximation
