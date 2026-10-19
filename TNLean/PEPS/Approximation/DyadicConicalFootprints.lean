/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicConicalGuides
import TNLean.PEPS.Approximation.DyadicFootprintTemplates

/-!
# An explicit footprint ratio near a mark

The small-patch covers of a point treatment need a footprint ratio `ν` such that every footprint
of radius `ν t` meets at most two labels of the sampled guide outside the inner holes of radius
`ε₀ t`. The source takes `ν` from the compactness observation over the finitely many templates
near a mark. This file proves the two-owner condition at the explicit ratio
`pointTreatmentRatio ε₀ = min(ε₀, 1) / 20000`, for every template and every reading after a
generic displacement:

* the templates are conical about the mark in units of `t`, with walls on lines whose normals
  lie in `wallNormals`; such a guide is locally constant off the lines through the mark with
  these normals (`eventually_eq_of_not_isWallDirection`, in
  `TNLean.PEPS.Approximation.DyadicConicalGuides`);
* in the cone `|w.2| ≤ w.1` the guide is a function of the slope `w.2 / w.1`, and the slopes of
  the wall directions there are multiples of `1/1000` (`le_abs_sub_of_mem_wallSlopes`); four
  isometric charts carry every point into this cone (`exists_isWallChart`);
* three nearby points far from the mark lie in a window of slopes of length below `1/1000`, which
  meets at most one wall slope, so they carry at most two labels
  (`eq_or_eq_or_eq_of_conical`); two nearby labels just outside the treated square are separated
  by one wall, which meets the rim of the square at a point approached by both labels
  (`exists_wall_near_of_conical`);
* hence, for a reading after a generic displacement, three labels in a footprint force a true
  vertex within `ε₀` of a footprint point: the mark itself when it is not treated, and a point of
  the rim of the treated square when it is (`hasTwoOwnerFootprints_reading_pointTreated`,
  `hasTwoOwnerFootprints_reading_footprintTemplate`).

The bound is crude: it uses only the slopes of the wall directions, not the actual layout of the
bands.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the walls of the guides
  (lines 69–80, 142–221), the straight-ray charts (lines 301–302), the point treatment (lines
  330–338), the compactness observation (lines 447–479) and the point covers (lines 481–505).
-/

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

/-! ### The two-owner condition near a mark -/

/-- After a generic displacement every point leaves the wall directions at once.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:73–77`. -/
theorem IsGenericDisplacement.eventually_not_isWallDirection {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) (u : ℝ × ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ IsWallDirection (u + ε • v) := by
  have h : ∀ N ∈ wallNormals, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      N.1 * (u + ε • v).1 + N.2 * (u + ε • v).2 ≠ 0 := by
    intro N hN
    have e (ε : ℝ) : N.1 * (u + ε • v).1 + N.2 * (u + ε • v).2 =
        (N.1 * u.1 + N.2 * u.2) + ε * (N.1 * v.1 + N.2 * v.2) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    by_cases h0 : N.1 * u.1 + N.2 * u.2 = 0
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [e, h0, zero_add]
      exact mul_ne_zero hε.ne' (hv N hN)
    · have hc : Continuous fun ε : ℝ => (N.1 * u.1 + N.2 * u.2) + ε * (N.1 * v.1 + N.2 * v.2) :=
        by fun_prop
      have := (hc.tendsto 0).eventually (isOpen_ne.mem_nhds (by simpa using h0))
      filter_upwards [nhdsWithin_le_nhds this] with ε hε
      rw [e]; exact hε
  filter_upwards [(finite_wallNormals.eventually_all).2 h] with ε hε
  rintro ⟨N, hN, h0⟩
  exact hε N hN h0

/-- A reading of a labelling that is constant near a point takes that value at the point.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:71–77`. -/
theorem IsDisplacedReading.eq_of_eventually_const {X ι : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [ContinuousAdd X] [ContinuousSMul ℝ X] {T F : X → ι} {v : X}
    (hT : IsDisplacedReading T F v) {y : X} {c : ι} (h : ∀ᶠ q in 𝓝 y, F q = c) : T y = c := by
  obtain ⟨ε, e₁, e₂⟩ := ((hT y).and ((tendsto_add_smul_nhdsGT y v).eventually h)).exists
  rw [e₁, e₂]

/-- **The explicit footprint ratio near a mark.** The ratio `min(ε₀, 1) / 20000`, in place of
the compactness minimum of the source over the templates near a mark. Three labels of a template
within a footprint lie in a window of slopes of length below `1/1000` at distance at least
`min(ε₀, 1)` from the mark, up to the displacement.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 481–505, 559–563`. -/
noncomputable def pointTreatmentRatio (ε₀ : ℝ) : ℝ := min ε₀ 1 / 20000

/-- The footprint ratio near a mark is positive.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:559–563`. -/
theorem pointTreatmentRatio_pos {ε₀ : ℝ} (hε : 0 < ε₀) : 0 < pointTreatmentRatio ε₀ := by
  unfold pointTreatmentRatio; have := lt_min hε one_pos; positivity

/-- The footprint ratio near a mark is at most `1/20000`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:481–505`. -/
theorem pointTreatmentRatio_le (ε₀ : ℝ) : pointTreatmentRatio ε₀ ≤ 1 / 20000 := by
  unfold pointTreatmentRatio; have := min_le_right ε₀ 1; linarith

/-- **The two-owner condition of a conical guide near a mark, at an explicit footprint radius.**
Let `G` be constant along the rays from the origin in the open square of radius `4`, and locally
constant there off the wall directions. Let `T` be a reading, after a generic displacement, of
the relabelling by `π` of `G` point treated on the unit square, or of `G` itself. Then `T` has
the two-owner condition with working set the closed square of radius `2`, holes of radius `ε₀`
at its true vertices within `3`, and every footprint radius `δ ≤ min(ε₀, 1) / 20000`.

The wall slopes are multiples of `1/1000`, so three labels in a footprint far from the origin
straddle at most one wall; if the origin is untreated it is a true vertex, and if it is treated a
label of the treated square meets two labels across one wall at a true vertex of the rim.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 481–505`. -/
theorem hasTwoOwnerFootprints_reading_pointTreated {κ ι : Type*} {G : ℝ × ℝ → κ}
    (hcon : ∀ (w : ℝ × ℝ) (a : ℝ), 0 < a → ‖w‖ < 4 → ‖a • w‖ < 4 → G (a • w) = G w)
    (hloc : ∀ y : ℝ × ℝ, ‖y‖ < 4 → ¬ IsWallDirection y → ∀ᶠ y' in 𝓝 y, G y' = G y)
    (π : κ → ι) (P : Option κ) {v : ℝ × ℝ} (hv : IsGenericDisplacement v) {T : ℝ × ℝ → ι}
    (hT : IsDisplacedReading T (fun u => π (pointTreated 0 1 P G u)) v) {ε₀ δ : ℝ}
    (hε : 0 < ε₀) (hδ : δ ≤ pointTreatmentRatio ε₀) :
    HasTwoOwnerFootprints T (closedBall 0 2)
      {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u} ε₀ δ := by
  intro x u₁ u₂ u₃ h₁ h₂ h₃
  by_contra hne
  push Not at hne
  obtain ⟨n12, n13, n23⟩ := hne
  set l := pointTreatmentRatio ε₀ with hl
  have hl0 : 0 < l := pointTreatmentRatio_pos hε
  have hlε : 20000 * l ≤ ε₀ := by
    rw [hl, pointTreatmentRatio]; have := min_le_left ε₀ 1; linarith
  have hl1 : 20000 * l ≤ 1 := by
    rw [hl, pointTreatmentRatio]; have := min_le_right ε₀ 1; linarith
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ × ℝ) + ε • v ∈ ball 0 l :=
    tendsto_add_smul_nhdsGT 0 v (ball_mem_nhds 0 hl0)
  obtain ⟨ε, e₁, e₂, e₃, e₄, g₁, g₂, g₃⟩ := ((hT u₁).and ((hT u₂).and ((hT u₃).and (hsmall.and
    ((hv.eventually_not_isWallDirection u₁).and ((hv.eventually_not_isWallDirection u₂).and
      (hv.eventually_not_isWallDirection u₃))))))).exists
  rw [zero_add, mem_ball, dist_zero_right] at e₄
  set w₁ := u₁ + ε • v
  set w₂ := u₂ + ε • v
  set w₃ := u₃ + ε • v
  -- distances
  have hd (u : ℝ × ℝ) : dist u (u + ε • v) < l := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left]; exact e₄
  have hx {u : ℝ × ℝ} (hu : u ∈ (closedBall x δ ∩ closedBall 0 2) \
      ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀) :
      dist u x ≤ δ ∧ ‖u‖ ≤ 2 :=
    ⟨hu.1.1, by simpa [mem_closedBall, dist_zero_right] using hu.1.2⟩
  have hw {u u' : ℝ × ℝ}
      (hu : u ∈ (closedBall x δ ∩ closedBall 0 2) \
        ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀)
      (hu' : u' ∈ (closedBall x δ ∩ closedBall 0 2) \
        ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀) :
      dist (u + ε • v) (u' + ε • v) ≤ 2 * l := by
    rw [dist_add_right]
    linarith [dist_triangle u x u', dist_comm x u', (hx hu).1, (hx hu').1]
  have d12 := hw h₁ h₂
  have d13 := hw h₁ h₃
  have d23 := hw h₂ h₃
  have hn {u : ℝ × ℝ}
      (hu : u ∈ (closedBall x δ ∩ closedBall 0 2) \
        ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀) :
      ‖u + ε • v‖ < 4 := by
    have := norm_add_le u (ε • v); linarith [(hx hu).2]
  have hn₁ := hn h₁
  have hn₂ := hn h₂
  have hn₃ := hn h₃
  -- a footprint point within `ε₀` of a true vertex within `3` is in a hole
  have hhole {u z : ℝ × ℝ}
      (hu : u ∈ (closedBall x δ ∩ closedBall 0 2) \
        ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀)
      (hz : ‖z‖ ≤ 3) (htv : IsTrueVertex T z) (hdz : dist u z < ε₀) : False :=
    hu.2 (mem_biUnion ⟨by rwa [mem_closedBall, dist_zero_right], htv⟩ hdz)
  -- the reading at points near which the guide is locally constant
  have hGread {y : ℝ × ℝ} (hy : ‖y‖ < 4) (hny : ¬ IsWallDirection y)
      (hF : ∀ᶠ q in 𝓝 y, pointTreated 0 1 P G q = G q) : T y = π (G y) :=
    hT.eq_of_eventually_const ((hF.and (hloc y hy hny)).mono fun q hq => by
      simp only [hq.1, hq.2])
  cases P with
  | none =>
    have hP : ∀ q, pointTreated 0 1 none G q = G q := fun _ => rfl
    simp only [hP] at e₁ e₂ e₃
    rw [e₁, e₂] at n12; rw [e₁, e₃] at n13; rw [e₂, e₃] at n23
    -- the origin is a true vertex
    have hcl {w : ℝ × ℝ} (hw4 : ‖w‖ < 4) (hnw : ¬ IsWallDirection w) :
        (0 : ℝ × ℝ) ∈ closure (T ⁻¹' {π (G w)}) := by
      rw [Metric.mem_closure_iff]
      intro τ hτ
      set a := min 1 (τ / (2 * (‖w‖ + 1))) with ha
      have ha0 : 0 < a := lt_min one_pos (by positivity)
      have ha1 : a ≤ 1 := min_le_left _ _
      have haτ : a ≤ τ / (2 * (‖w‖ + 1)) := min_le_right _ _
      have hnorm : ‖a • w‖ = a * ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
      have hay : ‖a • w‖ < 4 := by rw [hnorm]; nlinarith [norm_nonneg w]
      have hnay : ¬ IsWallDirection (a • w) := by rwa [isWallDirection_smul_iff ha0.ne']
      refine ⟨a • w, ?_, ?_⟩
      · rw [mem_preimage, mem_singleton_iff, hGread hay hnay (Eventually.of_forall hP),
          hcon w a ha0 hw4 hay]
      · rw [dist_zero_left, hnorm]
        have h2 : a * (2 * (‖w‖ + 1)) ≤ τ := (le_div_iff₀ (by positivity)).1 haτ
        nlinarith [norm_nonneg w]
    have htv : IsTrueVertex T 0 :=
      ⟨_, _, _, n12, n13, n23, hcl hn₁ g₁, hcl hn₂ g₂, hcl hn₃ g₃⟩
    have hfar : ε₀ ≤ ‖u₁‖ := by
      by_contra h
      exact hhole h₁ (by norm_num) htv (by rw [dist_zero_right]; linarith)
    have h1 : ε₀ - l ≤ ‖w₁‖ := by
      have := norm_sub_norm_le u₁ (-(ε • v))
      rw [sub_neg_eq_add, norm_neg] at this
      linarith
    rcases eq_or_eq_or_eq_of_conical hcon hloc h1 (D := 2 * l) (by linarith) d12 d13 d23 hn₁ hn₂
      hn₃ g₁ g₂ g₃ with h | h | h
    · exact n12 (congrArg π h)
    · exact n13 (congrArg π h)
    · exact n23 (congrArg π h)
  | some P₀ =>
    beta_reduce at e₁ e₂ e₃
    have hin {q : ℝ × ℝ} (hq : q ∈ ball (0 : ℝ × ℝ) 1) : pointTreated 0 1 (some P₀) G q = P₀ :=
      homogenize_of_mem hq
    have hout {q : ℝ × ℝ} (hq : q ∉ ball (0 : ℝ × ℝ) 1) :
        pointTreated 0 1 (some P₀) G q = G q :=
      homogenize_of_notMem hq
    have hone {q : ℝ × ℝ} (hq : q ∉ ball (0 : ℝ × ℝ) 1) : 1 ≤ ‖q‖ := by
      simpa [mem_ball, dist_zero_right] using hq
    -- the case of one treated point
    have key {ua ub uc : ℝ × ℝ}
        (ha : ua ∈ (closedBall x δ ∩ closedBall 0 2) \
          ⋃ h ∈ {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u}, ball h ε₀)
        (hba : ua + ε • v ∉ ball (0 : ℝ × ℝ) 1) (hbb : ub + ε • v ∉ ball (0 : ℝ × ℝ) 1)
        (hbc : uc + ε • v ∈ ball (0 : ℝ × ℝ) 1)
        (dab : dist (ua + ε • v) (ub + ε • v) ≤ 2 * l)
        (dac : dist (ua + ε • v) (uc + ε • v) ≤ 2 * l) (hna : ‖ua + ε • v‖ < 4)
        (hnb : ‖ub + ε • v‖ < 4) (ga : ¬ IsWallDirection (ua + ε • v))
        (gb : ¬ IsWallDirection (ub + ε • v)) (nab : π (G (ua + ε • v)) ≠ π (G (ub + ε • v)))
        (nac : π (G (ua + ε • v)) ≠ π P₀) (nbc : π (G (ub + ε • v)) ≠ π P₀) : False := by
      have h1 := hone hba
      have h1' : ‖ua + ε • v‖ ≤ 1 + 2 * l := by
        have := norm_le_norm_add_norm_sub' (ua + ε • v) (uc + ε • v)
        rw [← dist_eq_norm] at this
        rw [mem_ball, dist_zero_right] at hbc
        linarith
      obtain ⟨z, hz, hdz, hy₁, hy₂⟩ := exists_wall_near_of_conical hcon hloc h1 h1'
        (by linarith) dab hna hnb ga gb fun h => nab (congrArg π h)
      have hcl {w : ℝ × ℝ} (hy : ∀ τ > 0, ∃ y : ℝ × ℝ, dist y z < τ ∧ 1 < ‖y‖ ∧ ‖y‖ < 3 ∧
          ¬ IsWallDirection y ∧ G y = G w) : z ∈ closure (T ⁻¹' {π (G w)}) := by
        rw [Metric.mem_closure_iff]
        intro τ hτ
        obtain ⟨y, hyz, hy1, hy3, hny, hGy⟩ := hy τ hτ
        have hev : ∀ᶠ q in 𝓝 y, pointTreated 0 1 (some P₀) G q = G q := by
          have : ∀ᶠ q in 𝓝 y, 1 < ‖q‖ :=
            continuous_norm.continuousAt.eventually (lt_mem_nhds hy1)
          filter_upwards [this] with q hq
          exact hout (by rw [mem_ball, dist_zero_right]; linarith)
        refine ⟨y, ?_, by rwa [dist_comm]⟩
        rw [mem_preimage, mem_singleton_iff, hGread (by linarith) hny hev, hGy]
      have hclP : z ∈ closure (T ⁻¹' {π P₀}) := by
        rw [Metric.mem_closure_iff]
        intro τ hτ
        set s := min (1 / 2) (τ / 2) with hs
        have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
        have hs1 : s ≤ 1 / 2 := min_le_left _ _
        have hsτ : s ≤ τ / 2 := min_le_right _ _
        have hyin : (1 - s) • z ∈ ball (0 : ℝ × ℝ) 1 := by
          rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
            hz]
          linarith
        refine ⟨(1 - s) • z, ?_, ?_⟩
        · rw [mem_preimage, mem_singleton_iff]
          exact hT.eq_of_eventually_const (Filter.eventually_of_mem (isOpen_ball.mem_nhds hyin)
            fun q hq => by simp only [hin hq])
        · rw [dist_eq_norm, show z - (1 - s) • z = s • z by rw [sub_smul, one_smul]; abel,
            norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hz]
          linarith
      have htv : IsTrueVertex T z := ⟨_, _, _, nab, nac, nbc, hcl hy₁, hcl hy₂, hclP⟩
      refine hhole ha (by rw [hz]; norm_num) htv ?_
      linarith [dist_triangle ua (ua + ε • v) z, hd ua]
    by_cases b₁ : w₁ ∈ ball (0 : ℝ × ℝ) 1 <;> by_cases b₂ : w₂ ∈ ball (0 : ℝ × ℝ) 1 <;>
      by_cases b₃ : w₃ ∈ ball (0 : ℝ × ℝ) 1
    · exact n12 (by rw [e₁, e₂, hin b₁, hin b₂])
    · exact n12 (by rw [e₁, e₂, hin b₁, hin b₂])
    · exact n13 (by rw [e₁, e₃, hin b₁, hin b₃])
    · rw [e₁, e₂, hin b₁, hout b₂] at n12
      rw [e₁, e₃, hin b₁, hout b₃] at n13
      rw [e₂, e₃, hout b₂, hout b₃] at n23
      rw [dist_comm] at d12 d13
      exact key h₂ b₂ b₃ b₁ d23 d12 hn₂ hn₃ g₂ g₃ n23 (Ne.symm n12) (Ne.symm n13)
    · exact n23 (by rw [e₂, e₃, hin b₂, hin b₃])
    · rw [e₁, e₂, hout b₁, hin b₂] at n12
      rw [e₁, e₃, hout b₁, hout b₃] at n13
      rw [e₂, e₃, hin b₂, hout b₃] at n23
      exact key h₁ b₁ b₃ b₂ d13 d12 hn₁ hn₃ g₁ g₃ n13 n12 (Ne.symm n23)
    · rw [e₁, e₂, hout b₁, hout b₂] at n12
      rw [e₁, e₃, hout b₁, hin b₃] at n13
      rw [e₂, e₃, hout b₂, hin b₃] at n23
      exact key h₁ b₁ b₂ b₃ d12 d13 hn₁ hn₂ g₁ g₂ n12 n13 n23
    · rw [e₁, e₂, hout b₁, hout b₂] at n12
      rw [e₁, e₃, hout b₁, hout b₃] at n13
      rw [e₂, e₃, hout b₂, hout b₃] at n23
      rcases eq_or_eq_or_eq_of_conical hcon hloc (hone b₁) (D := 2 * l) (by linarith) d12 d13
        d23 hn₁ hn₂ hn₃ g₁ g₂ g₃ with h | h | h
      · exact n12 (congrArg π h)
      · exact n13 (congrArg π h)
      · exact n23 (congrArg π h)

/-- **The two-owner condition of the templates near a mark, at an explicit footprint radius.**
Every reading after a generic displacement of a template of the point treatment has the two-owner
condition with working set the closed square of radius `2`, holes of radius `ε₀` at its true
vertices within `3`, and every footprint radius `δ ≤ pointTreatmentRatio ε₀`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:447–479, 481–505`. -/
theorem hasTwoOwnerFootprints_reading_footprintTemplate (i : TemplateIndex) {v : ℝ × ℝ}
    (hv : IsGenericDisplacement v) {T : ℝ × ℝ → BlockSlot 1}
    (hT : IsDisplacedReading T (footprintTemplate i) v) {ε₀ δ : ℝ} (hε : 0 < ε₀)
    (hδ : δ ≤ pointTreatmentRatio ε₀) :
    HasTwoOwnerFootprints T (closedBall 0 2)
      {u | u ∈ closedBall (0 : ℝ × ℝ) 3 ∧ IsTrueVertex T u} ε₀ δ := by
  set c := i.2.1.1
  have hR : IsConicalAt referenceRepainting.guide c := by
    intro w a b ha hb haw hbw
    have := isConicalAt_blockGuide (blockSlot 1) i.2.1.2 w a b ha hb haw hbw
    simpa only [referenceRepainting, blockBaseline, blockCorner, Int.cast_zero, mul_zero,
      Prod.mk_zero_zero, add_zero] using this
  have hc := RepaintingBaseline.IsUnmodifiedGuide.isConicalAt _ rfl i.2.1.2 hR i.1.2
  have hcon : ∀ (w : ℝ × ℝ) (a : ℝ), 0 < a → ‖w‖ < 4 → ‖a • w‖ < 4 →
      i.1.1 (c + (1 / 32 : ℝ) • (a • w)) = i.1.1 (c + (1 / 32 : ℝ) • w) := by
    intro w a ha hw haw
    rw [smul_smul]
    refine hc w _ _ (by positivity) (by norm_num) ?_ ?_
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at haw
      nlinarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      linarith
  have h0 : HasLineWalls wallNormals i.1.1 :=
    i.1.2.hasLineWalls _ ((hasLineWalls_blockGuide 1 (blockSlot 1)).comp_add _)
  have hw : HasLineWalls wallNormals fun u => i.1.1 (c + (1 / 32 : ℝ) • u) :=
    h0.comp_affine c (by norm_num)
  exact hasTwoOwnerFootprints_reading_pointTreated (G := fun u => i.1.1 (c + (1 / 32 : ℝ) • u))
    hcon (fun y hy hny => eventually_eq_of_not_isWallDirection hcon hw hy hny) i.2.2.2 i.2.2.1
    hv hT hε hδ

end TNLean.PEPS.Approximation
