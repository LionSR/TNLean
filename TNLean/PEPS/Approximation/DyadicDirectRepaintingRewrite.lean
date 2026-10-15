/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicFootprintScaling
import TNLean.PEPS.Approximation.DyadicPatchRewriteGates
import TNLean.PEPS.Approximation.DyadicSampledGuides
import TNLean.PEPS.Approximation.GuideFrameRewrite

/-!
# The direct repainting of a square as a small-patch rewrite

For `n ≤ K₀ t` the protocol of Proposition 7.1 repaints a square of side `n` directly, by one
small-patch rewrite whose patches form a fine net over the square and the affected outer holes at
its four corners (`06-geometry.tex`, lines 507–527). This file checks the plane conditions of
Lemma 6.3 (`GuideFrameRewrite.PlaneConditions`) for this rewrite, between the frames of the
readings of two guides uniform on the `n`-blocks that differ only on the block `S`, with holes of
radius `r` at given finite sets of true vertices, given patches of radius `u` on the net, and the
two-owner condition of the readings near the block as a hypothesis
(`exists_directRepainting_planeConditions`). The two-owner condition is
`exists_directRepainting_footprintRatio_reading` for `2 u = ν n`.

The untouched holes are the holes at the true vertices other than the corners of `S`; the
affected holes are those at its corners. The specified parties are the parties of the labels of
the nine blocks around `S`, in the two guides.

## Main definitions

* `Approximation.squareCorners`, `Approximation.closedBlock`.

## Main results

* `Approximation.exists_directRepainting_planeConditions`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the readings of the
  guides at the sites (lines 69–80), the holes at true vertices (lines 102–125), the direct
  repainting by one small-patch rewrite (lines 507–527); Lemma 6.3 `lem:small-rewrite`,
  `05-frames.tex`, lines 188–218.
-/

open Set Metric Filter Topology

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame

/-! ### Corners and neighbouring blocks of a block -/

/-- The four corners of the block `S` of side `n`. -/
def squareCorners (n : ℝ) (S : ℤ × ℤ) : Finset (ℝ × ℝ) :=
  open Classical in
  (({0, 1} : Finset ℤ) ×ˢ ({0, 1} : Finset ℤ)).image fun d => blockCorner n (S.1 + d.1, S.2 + d.2)

theorem card_squareCorners_le (n : ℝ) (S : ℤ × ℤ) : (squareCorners n S).card ≤ 4 := by
  classical
  exact Finset.card_image_le.trans (by decide)

theorem card_blockWindow_one : (blockWindow 1).card = 9 := by
  decide

theorem blockCorner_injective {n : ℝ} (hn : 0 < n) : Function.Injective (blockCorner n) := by
  intro Q Q' h
  simp only [blockCorner, Prod.mk.injEq, mul_right_inj' hn.ne', Int.cast_inj] at h
  exact Prod.ext h.1 h.2

theorem mem_squareCorners_iff {n : ℝ} (hn : 0 < n) {S Q : ℤ × ℤ} :
    blockCorner n Q ∈ squareCorners n S ↔ IsBlockCornerOf S Q := by
  classical
  simp only [squareCorners, Finset.mem_image, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨d1, d2⟩, ⟨h1, h2⟩, he⟩
    obtain rfl := blockCorner_injective hn he
    unfold IsBlockCornerOf
    dsimp only at h1 h2
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(Q.1 - S.1, Q.2 - S.2), ⟨by omega, by omega⟩, ?_⟩
    simp

theorem sub_mem_closedSquare_of_mem_squareCorners {n : ℝ} (hn : 0 < n) {S : ℤ × ℤ}
    {c : ℝ × ℝ} (hc : c ∈ squareCorners n S) : c - blockCorner n S ∈ closedSquare n := by
  classical
  obtain ⟨⟨d1, d2⟩, hd, rfl⟩ := Finset.mem_image.1 hc
  simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hd
  refine mem_closedSquare.2 ?_
  simp only [blockCorner, Prod.fst_sub, Prod.snd_sub]
  push_cast
  obtain ⟨h1 | h1, h2 | h2⟩ := hd <;> subst h1 h2 <;>
    simp only [Int.cast_zero, Int.cast_one, mul_add, mul_one, add_zero] <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-! ### Readings of guides that differ on one block -/

section Readings

variable {κ : Type} {n : ℝ} (hn : 0 < n) {S : ℤ × ℤ}

/-- The points of the closed block `S`. -/
def closedBlock (n : ℝ) (S : ℤ × ℤ) : Set (ℝ × ℝ) := {p | p - blockCorner n S ∈ closedSquare n}

theorem isClosed_closedBlock (n : ℝ) (S : ℤ × ℤ) : IsClosed (closedBlock n S) :=
  (isClosed_Icc.prod isClosed_Icc).preimage (continuous_id.sub continuous_const)

include hn

/-- Two block guides that differ only on the block `S` agree off the closed block. -/
theorem blockGuide_eq_of_notMem_closedBlock {lab lab' : ℤ × ℤ → κ}
    (hlab : ∀ Q, Q ≠ S → lab' Q = lab Q) {p : ℝ × ℝ} (hp : p ∉ closedBlock n S) :
    blockGuide n lab p = blockGuide n lab' p := by
  have hne := blockIndex_ne_of_notMem_closedSquare hn S (p := p - blockCorner n S) hp
  rw [sub_add_cancel] at hne
  exact (hlab _ hne).symm

/-- Readings of two block guides that differ only on the block `S` differ only on the closed
block. -/
theorem mem_closedBlock_of_reading_ne {lab lab' : ℤ × ℤ → κ}
    (hlab : ∀ Q, Q ≠ S → lab' Q = lab Q) {v : ℝ × ℝ} {g g' : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v)
    (hg' : IsDisplacedReading g' (blockGuide n lab') v) {p : ℝ × ℝ} (hp : g p ≠ g' p) :
    p ∈ closedBlock n S := by
  have h := hg.ne_subset_closure hg' hp
  refine closure_minimal (fun x hx => ?_) (isClosed_closedBlock n S) h
  by_contra hx'
  exact hx (blockGuide_eq_of_notMem_closedBlock hn hlab hx')

/-- Readings of two block guides that differ only on the block `S` agree near every point at
distance more than zero from the closed block. -/
theorem reading_eventuallyEq {lab lab' : ℤ × ℤ → κ} (hlab : ∀ Q, Q ≠ S → lab' Q = lab Q)
    {v : ℝ × ℝ} {g g' : ℝ × ℝ → κ} (hg : IsDisplacedReading g (blockGuide n lab) v)
    (hg' : IsDisplacedReading g' (blockGuide n lab') v) {c : ℝ × ℝ}
    (hc : c ∉ closedBlock n S) : g =ᶠ[𝓝 c] g' := by
  filter_upwards [(isClosed_closedBlock n S).isOpen_compl.mem_nhds hc] with p hp
  by_contra hne
  exact hp (mem_closedBlock_of_reading_ne hn hlab hg hg' hne)

/-- The label of a reading at a point within `n` of the closed block `S` is a label of one of the
nine blocks around `S`. -/
theorem reading_mem_blockWindow {lab : ℤ × ℤ → κ} {v : ℝ × ℝ} {g : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v) {p y : ℝ × ℝ} (hy : y ∈ closedBlock n S)
    (hp : dist p y < n) : ∃ R ∈ blockWindow 1, g p = lab (R + S) := by
  have hε := (tendsto_add_smul_nhdsGT p v).eventually
    ((isOpen_lt (continuous_id.dist continuous_const) continuous_const).mem_nhds
      (show dist p y < n from hp))
  obtain ⟨ε, e₁, e₂⟩ := ((hg p).and hε).exists
  obtain ⟨a, b⟩ := abs_blockIndex_sub_le hn hy (show dist (p + ε • v) y < n from e₂)
  refine ⟨blockIndex n (p + ε • v) - S, ?_, by rw [sub_add_cancel]; exact e₁⟩
  simp only [blockWindow, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
  rw [abs_le] at a b
  push_cast
  omega

/-- An incident label of a reading at a point of the closed block `S` is a label of one of the
nine blocks around `S`. -/
theorem incidentLabel_mem_blockWindow {lab : ℤ × ℤ → κ} {v : ℝ × ℝ} {g : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v) {c : ℝ × ℝ} (hc : c ∈ closedBlock n S)
    {l : κ} (hl : l ∈ incidentLabels g c) : ∃ R ∈ blockWindow 1, l = lab (R + S) := by
  obtain ⟨p, hp, hpc⟩ := Metric.mem_closure_iff.1 hl n hn
  obtain ⟨R, hR, e⟩ := reading_mem_blockWindow hn hg hc (by rwa [dist_comm])
  exact ⟨R, hR, (mem_singleton_iff.1 hp).symm.trans e⟩

end Readings

/-- A point of the closed block `S` is within `n` of its corner. -/
theorem dist_blockCorner_le_of_mem_closedBlock {n : ℝ} {S : ℤ × ℤ} {y : ℝ × ℝ}
    (hy : y ∈ closedBlock n S) : dist y (blockCorner n S) ≤ n := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 hy
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le, abs_le]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- A point of the closed block `S` is within `n / 2` of its center. -/
theorem dist_center_le_of_mem_closedBlock {n : ℝ} {S : ℤ × ℤ} {y : ℝ × ℝ}
    (hy : y ∈ closedBlock n S) : dist y (blockCorner n S + (n / 2, n / 2)) ≤ n / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_closedSquare.1 hy
  simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq, abs_le, abs_le]
  simp only [Prod.fst_add, Prod.snd_add]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-! ### The plane conditions of the direct repainting -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

/-- **The direct repainting satisfies the plane conditions of Lemma 6.3.** Let `g` and `g'` be
the readings along `v` of two guides uniform on the `n`-blocks with labels `lab` and `lab'` that
differ only on the block `S`, and let `V`, `V'` be finite sets of true vertices of `g`, `g'`
containing every true vertex within `3 n` of the corner of `S` and agreeing away from the corners
of `S`. Let the holes have radius `r` and the patches radius `u`, with `3 u + 4 r < n`, and
suppose that both readings satisfy the two-owner condition for footprints of radius `2 u` in the
ball of radius `2 n` about the corner of `S`, outside the open inner holes of radius `r` at their
true vertices within `3 n`. Then there is a rewrite between the frames of `g` with holes at `V`
and of `g'` with holes at `V'`, with patches on a net over the block and the affected outer holes,
satisfying the plane conditions of Lemma 6.3. It has at most four affected holes in each frame,
at most `(2 (n / 2 + 2 r + u) / u + 1)²` patches, and a nonempty list of at most `18` specified
parties, each the party of the old or the new label of one of the nine blocks around `S`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527; Lemma 6.3 `lem:small-rewrite`,
`05-frames.tex`, lines 188–207. -/
theorem exists_directRepainting_planeConditions {n r u : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hu : 0 < u) (hsep : 3 * u + 4 * r < n) {lab lab' : ℤ × ℤ → κ} {S : ℤ × ℤ}
    (hlab : ∀ Q, Q ≠ S → lab' Q = lab Q) {v : ℝ × ℝ} {g g' : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v)
    (hg' : IsDisplacedReading g' (blockGuide n lab') v) (own : κ → Party) (ph : κ)
    (rank : κ → ℕ) {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g c)
    (hV' : ∀ c ∈ V', IsTrueVertex g' c)
    (hVc : ∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g c → c ∈ V)
    (hVc' : ∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g' c → c ∈ V')
    (hVV' : ∀ c ∉ squareCorners n S, (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = r)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (htwo : HasTwoOwnerFootprints g (closedBall (blockCorner n S) (2 * n))
      {c | c ∈ closedBall (blockCorner n S) (3 * n) ∧ IsTrueVertex g c} r (2 * u))
    (htwo' : HasTwoOwnerFootprints g' (closedBall (blockCorner n S) (2 * n))
      {c | c ∈ closedBall (blockCorner n S) (3 * n) ∧ IsTrueVertex g' c} r (2 * u)) :
    ∃ G : GuideFrameRewrite pos q κ Party, G.PlaneConditions ∧ G.old = g ∧ G.new = g' ∧
      G.own = own ∧ G.ph = ph ∧ G.rank = rank ∧ G.holeOld = hole ∧ G.holeNew = hole ∧
      G.patch = patch ∧ G.untouched ∪ G.oldAffected = V ∧ G.untouched ∪ G.newAffected = V' ∧
      G.oldAffected.card ≤ 4 ∧ G.newAffected.card ≤ 4 ∧
      (G.centers.card : ℝ) ≤ (2 * (n / 2 + 2 * r + u) / u + 1) ^ 2 ∧ G.parties.card ≤ 18 ∧
      G.parties.Nonempty ∧
      ∀ x ∈ G.parties, ∃ R ∈ blockWindow 1, x = own (lab (R + S)) ∨ x = own (lab' (R + S)) := by
  classical
  set B := closedBlock n S
  set K : Set (ℝ × ℝ) := {p | ∃ y ∈ B, dist p y ≤ 2 * r}
  have hK : K ⊆ closedBall (blockCorner n S + (n / 2, n / 2)) (n / 2 + 2 * r) := by
    rintro p ⟨y, hy, hpy⟩
    exact mem_closedBall.2 (by linarith [dist_triangle p y (blockCorner n S + (n / 2, n / 2)),
      dist_center_le_of_mem_closedBlock hy])
  obtain ⟨s, hcard, hcov, hnear⟩ := exists_netCover hu (by positivity) hK
  have hKB : ∀ y ∈ B, y ∈ K := fun y hy => ⟨y, hy, by rw [dist_self]; positivity⟩
  have hcB : ∀ c ∈ squareCorners n S, c ∈ B := fun c hc =>
    sub_mem_closedSquare_of_mem_squareCorners hn hc
  have hbc : ∀ c ∈ V, ∃ Q, c = blockCorner n Q := fun c hc =>
    (hg.isTrueVertex (hV c hc)).eq_blockCorner hn
  have hbc' : ∀ c ∈ V', ∃ Q, c = blockCorner n Q := fun c hc =>
    (hg'.isTrueVertex (hV' c hc)).eq_blockCorner hn
  have hfar : ∀ c ∈ V, c ∉ squareCorners n S → ∀ y ∈ B, n ≤ dist y c := by
    intro c hc hnc y hy
    obtain ⟨Q, rfl⟩ := hbc c hc
    exact le_dist_blockCorner hn (fun hQ => hnc ((mem_squareCorners_iff hn).2 hQ)) hy
  have hpair : ∀ W : Finset (ℝ × ℝ), (∀ c ∈ W, ∃ Q, c = blockCorner n Q) →
      (W : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer := by
    intro W hW z hz z' hz' hne
    obtain ⟨Q, rfl⟩ := hW z hz
    obtain ⟨Q', rfl⟩ := hW z' hz'
    have hd := le_dist_blockCorner_of_ne hn (fun h : Q = Q' => hne (h ▸ rfl))
    refine disjoint_outer_of_disjoint_closedBall ?_
    rw [(hhole _).1, (hhole _).2, (hhole _).1, (hhole _).2]
    exact closedBall_disjoint_closedBall (by linarith)
  set U := V.filter (· ∉ squareCorners n S) with hUdef
  set A := V.filter (· ∈ squareCorners n S) with hAdef
  set A' := V'.filter (· ∈ squareCorners n S) with hA'def
  have hUA : U ∪ A = V := by
    ext c
    by_cases hc : c ∈ squareCorners n S <;> simp [U, A, hc]
  have hUA' : U ∪ A' = V' := by
    ext c
    by_cases hc : c ∈ squareCorners n S
    · simp [U, A', hc]
    · simp [U, A', hc, hVV' c hc]
  have hdU : Disjoint U A := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    exact (Finset.mem_filter.1 hc).2 (Finset.mem_filter.1 hc').2
  have hdU' : Disjoint U A' := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    exact (Finset.mem_filter.1 hc).2 (Finset.mem_filter.1 hc').2
  let G : GuideFrameRewrite pos q κ Party :=
    { old := g, new := g', own := own, ph := ph, rank := rank, untouched := U,
      oldAffected := A, newAffected := A', holeOld := hole, holeNew := hole,
      centers := s.image (blockCorner u), patch := patch,
      parties := ((blockWindow 1).image (fun R => lab (R + S)) ∪
        (blockWindow 1).image (fun R => lab' (R + S))).image own,
      disjoint_untouched_old := hdU, disjoint_untouched_new := hdU'
      pairwise_old := by rw [hUA]; exact hpair V hbc
      pairwise_new := by rw [hUA']; exact hpair V' hbc' }
  -- every point of an outer patch square is within `3 u + 2 r` of the closed block
  have hnearB : ∀ z ∈ G.centers, ∀ p, dist p (patch z).center ≤ 2 * (patch z).scale →
      ∃ b ∈ B, dist p b < 3 * u + 2 * r := by
    intro z hz p hp
    obtain ⟨y, ⟨b, hb, hyb⟩, hpy⟩ := exists_dist_lt_of_mem_image hpatch hnear z hz p hp
    exact ⟨b, hb, by linarith [dist_triangle p y b]⟩
  have hcover := exists_mem_image_dist_le_scale hpatch hcov
  have hparty : ∀ p, ∀ b ∈ B, dist p b < n → own (g p) ∈ G.parties ∧ own (g' p) ∈ G.parties := by
    intro p b hb hpb
    obtain ⟨Q, hQ, e⟩ := reading_mem_blockWindow hn hg hb hpb
    obtain ⟨Q', hQ', e'⟩ := reading_mem_blockWindow hn hg' hb hpb
    exact ⟨Finset.mem_image.2 ⟨lab (Q + S), Finset.mem_union_left _
      (Finset.mem_image_of_mem _ hQ), e.symm ▸ rfl⟩, Finset.mem_image.2 ⟨lab' (Q' + S),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ'), e'.symm ▸ rfl⟩⟩
  have hU : ∀ c ∈ U, c ∈ V ∧ c ∉ squareCorners n S := fun c hc => Finset.mem_filter.1 hc
  have hA : ∀ a ∈ A, a ∈ squareCorners n S := fun a ha => (Finset.mem_filter.1 ha).2
  have hA' : ∀ a ∈ A', a ∈ squareCorners n S := fun a ha => (Finset.mem_filter.1 ha).2
  have hfarU : ∀ c ∈ U, ∀ y ∈ B, n ≤ dist y c := fun c hc => hfar c (hU c hc).1 (hU c hc).2
  have hlabels : ∀ (g₀ : ℝ × ℝ → κ) (W : Finset (ℝ × ℝ)),
      (∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g₀ c → c ∈ W) →
      HasTwoOwnerFootprints g₀ (closedBall (blockCorner n S) (2 * n))
        {c | c ∈ closedBall (blockCorner n S) (3 * n) ∧ IsTrueVertex g₀ c} r (2 * u) →
      ∀ z ∈ G.centers, ∀ p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        dist p (patch z).center ≤ 2 * (patch z).scale ∧ ∀ c ∈ W, r ≤ dist p c) →
      g₀ p₁ = g₀ p₂ ∨ g₀ p₁ = g₀ p₃ ∨ g₀ p₂ = g₀ p₃ := by
    intro g₀ W hW htw z hz p₁ p₂ p₃ hp
    have mem : ∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        p ∈ (closedBall z (2 * u) ∩ closedBall (blockCorner n S) (2 * n)) \
          ⋃ h ∈ {c | c ∈ closedBall (blockCorner n S) (3 * n) ∧ IsTrueVertex g₀ c}, ball h r := by
      intro p hpm
      obtain ⟨h1, h2⟩ := hp p hpm
      obtain ⟨b, hb, hpb⟩ := hnearB z hz p h1
      have hz' : (patch z).center = z := (hpatch z).1
      rw [hz', (hpatch z).2] at h1
      refine ⟨⟨mem_closedBall.2 h1, mem_closedBall.2 ?_⟩, ?_⟩
      · linarith [dist_triangle p b (blockCorner n S), dist_blockCorner_le_of_mem_closedBlock hb]
      · simp only [mem_iUnion, mem_ball, not_exists, not_lt]
        exact fun c hc => h2 c (hW c hc.1 hc.2)
    exact htw z p₁ p₂ p₃ (mem p₁ (by simp)) (mem p₂ (by simp)) (mem p₃ (by simp))
  refine ⟨G, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, hUA, hUA', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the untouched holes agree
    intro c hc
    refine ⟨rfl, incidentLabels_congr (reading_eventuallyEq hn hlab hg hg' fun hcB' => ?_)⟩
    have := hfarU c hc c hcB'
    rw [dist_self] at this
    linarith
  · -- outer patch squares avoid the untouched holes
    intro z hz c hc p hp
    obtain ⟨b, hb, hpb⟩ := hnearB z hz p hp
    have := hfarU c hc b hb
    rw [(hhole c).1, (hhole c).2]
    linarith [dist_triangle b p c, dist_comm p b]
  · intro a ha c hc p hp
    have := hfarU c hc a (hcB a (hA a ha))
    rw [(hhole a).1, (hhole a).2] at hp
    rw [(hhole c).1, (hhole c).2]
    linarith [dist_triangle a p c, dist_comm p a]
  · intro a ha c hc p hp
    have := hfarU c hc a (hcB a (hA' a ha))
    change dist p (hole a).center ≤ 2 * (hole a).scale at hp
    rw [(hhole a).1, (hhole a).2] at hp
    change 2 * (hole c).scale < dist p (hole c).center
    rw [(hhole c).1, (hhole c).2]
    linarith [dist_triangle a p c, dist_comm p a]
  · -- the owner changes only on the block
    intro p hp
    have hne : g p ≠ g' p := fun e => hp (by change own (g p) = own (g' p); rw [e])
    exact hcover p (hKB p (mem_closedBlock_of_reading_ne hn hlab hg hg' hne))
  · intro a ha p hp
    rw [(hhole a).1, (hhole a).2] at hp
    exact hcover p ⟨a, hcB a (hA a ha), hp⟩
  · intro a ha p hp
    change dist p (hole a).center ≤ 2 * (hole a).scale at hp
    rw [(hhole a).1, (hhole a).2] at hp
    exact hcover p ⟨a, hcB a (hA' a ha), hp⟩
  · intro z hz p₁ h₁ p₂ h₂ p₃ h₃
    refine hlabels g V hVc htwo z hz p₁ p₂ p₃ fun p hp => ?_
    have hp' : p ∈ G.outsideOld z :=
      Set.insert_subset h₁ (Set.insert_subset h₂ (Set.singleton_subset_iff.2 h₃)) hp
    refine ⟨hp'.1, fun c hc => ?_⟩
    have := hp'.2 c (by change c ∈ U ∪ A; rw [hUA]; exact hc)
    rwa [(hhole c).1, (hhole c).2] at this
  · intro z hz p₁ h₁ p₂ h₂ p₃ h₃
    refine hlabels g' V' hVc' htwo' z hz p₁ p₂ p₃ fun p hp => ?_
    have hp' : p ∈ G.outsideNew z :=
      Set.insert_subset h₁ (Set.insert_subset h₂ (Set.singleton_subset_iff.2 h₃)) hp
    refine ⟨hp'.1, fun c hc => ?_⟩
    have := hp'.2 c (by change c ∈ U ∪ A'; rw [hUA']; exact hc)
    rwa [(hhole c).1, (hhole c).2] at this
  · -- owners on the footprints
    rintro p (⟨z, hz, hp⟩ | ⟨a, ha, hp⟩ | ⟨a, ha, hp⟩)
    · obtain ⟨b, hb, hpb⟩ := hnearB z hz p hp
      exact hparty p b hb (by linarith)
    · rw [(hhole a).1, (hhole a).2] at hp
      exact hparty p a (hcB a (hA a ha)) (by linarith)
    · change dist p (hole a).center ≤ 2 * (hole a).scale at hp
      rw [(hhole a).1, (hhole a).2] at hp
      exact hparty p a (hcB a (hA' a ha)) (by linarith)
  · -- affected tag holders
    intro a ha
    have hl := (isTagHolder_tagHolder (rank := rank) (ph := ph)
      (hV a (Finset.mem_filter.1 ha).1)).1
    obtain ⟨Q, hQ, e⟩ := incidentLabel_mem_blockWindow hn hg (hcB a (hA a ha)) hl
    exact Finset.mem_image.2 ⟨lab (Q + S), Finset.mem_union_left _
      (Finset.mem_image_of_mem _ hQ), congrArg own e.symm⟩
  · intro a ha
    have hl := (isTagHolder_tagHolder (rank := rank) (ph := ph)
      (hV' a (Finset.mem_filter.1 ha).1)).1
    obtain ⟨Q, hQ, e⟩ := incidentLabel_mem_blockWindow hn hg' (hcB a (hA' a ha)) hl
    exact Finset.mem_image.2 ⟨lab' (Q + S), Finset.mem_union_right _
      (Finset.mem_image_of_mem _ hQ), congrArg own e.symm⟩
  · exact (Finset.card_le_card fun a ha => hA a ha).trans (card_squareCorners_le n S)
  · exact (Finset.card_le_card fun a ha => hA' a ha).trans (card_squareCorners_le n S)
  · exact (Nat.cast_le.2 Finset.card_image_le).trans hcard
  · refine Finset.card_image_le.trans ((Finset.card_union_le _ _).trans ?_)
    have h1 := Finset.card_image_le (s := blockWindow 1) (f := fun R => lab (R + S))
    have h2 := Finset.card_image_le (s := blockWindow 1) (f := fun R => lab' (R + S))
    rw [card_blockWindow_one] at h1 h2
    omega
  · exact ⟨own (lab (0 + S)), Finset.mem_image_of_mem _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun R => lab (R + S)) (by decide)))⟩
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
    rcases Finset.mem_union.1 hl with hl | hl <;> obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hl
    · exact ⟨Q, hQ, Or.inl rfl⟩
    · exact ⟨Q, hQ, Or.inr rfl⟩

end TNLean.PEPS.Approximation
