/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairChildStarStep
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionMetric

/-!
# Isolated stars and contacts of the actual repair stages

Fix `0 < a₀ ≤ 1/4` and a stopping scale for which the metric hypotheses hold.
If every mark of one generation has an isolated star of radius `a₀` times its
scale, then:

* the assignment read from the current regions at a parent agrees with the
  wedge assignment of its star;
* every mark of the next generation has an isolated star of radius `a₀` times
  its scale;
* a replacement meets a distinct identifier of the same label only at marks
  of the next generation.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417, and
`geometry:repair-induction`, lines 471–514.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Written from the manuscript; no upstream Lean text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-- The assignment chosen from the current regions in the working square of
half-side `6 d(S)` agrees with the wedge assignment of an isolated star of a
larger radius.
Source: area-law Section 11, `geometry:repair-induction`, lines 486–496. -/
theorem repairCurrentSectorAssignment_eq {ι : Type*} [Nonempty ι] {R : ι → Set (ℝ × ℝ)}
    {v : ℝ × ℝ} {r ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    {σ : RepairFanSlot → ι}
    (hcl : ∀ i, closure (R i) ∩ Metric.ball v r = repairSectorSet σ v i ∩ Metric.ball v r)
    (hsub : ∀ s, interior (repairCurrentFanTriangle v r s) ⊆ R (σ s)) (s : RepairFanSlot) :
    repairCurrentSectorAssignment R v ρ s = σ s := by
  have hr : 0 < r := hρ.trans_le hρr
  have hmono : repairCurrentFanTriangle v ρ s ⊆ repairCurrentFanTriangle v r s := by
    intro x hx
    rw [mem_repairCurrentFanTriangle_iff hρ] at hx
    rw [mem_repairCurrentFanTriangle_iff hr]
    exact ⟨hx.1, hx.2.trans hρr⟩
  have hspec : interior (repairCurrentFanTriangle v ρ s) ⊆
      R (repairCurrentSectorAssignment R v ρ s) :=
    Classical.epsilon_spec (p := fun i ↦ interior (repairCurrentFanTriangle v ρ s) ⊆ R i)
      ⟨σ s, (interior_mono hmono).trans (hsub s)⟩
  set z := v + (ρ / 6) • (repairFanStart s + repairFanDirection s)
  have hz : z ∈ interior (repairCurrentFanTriangle v ρ s) := by
    rw [interior_repairCurrentFanTriangle hρ]
    have h1 := repairCross_start_direction s
    refine ⟨?_, ?_⟩
    · simp only [z, add_sub_cancel_left, repairFanOpenCone, Set.mem_ofPred_eq]
      simp only [repairCross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at h1 ⊢
      constructor <;> nlinarith
    · rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity)]
      have := norm_add_le (repairFanStart s) (repairFanDirection s)
      rw [norm_repairFanStart, norm_repairFanDirection] at this
      nlinarith
  have hzR := hspec hz
  have hzb : z ∈ Metric.ball v r := by
    rw [interior_repairCurrentFanTriangle hρ] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [hz.2]
  obtain ⟨⟨u, hu, hzu⟩, -⟩ := (hcl _).subset ⟨subset_closure hzR, hzb⟩
  rw [interior_repairCurrentFanTriangle hρ] at hz
  rw [← hu, eq_of_mem_repairFanOpenCone_of_mem_repairFanCone hz.1 hzu]

/-- Every point with coordinates in `{-1, 0, 1}` is a child offset.
Auxiliary to area-law Section 11, lines 404–409. -/
theorem exists_repairChildOffset_eq {y : ℝ × ℝ} (h₁ : y.1 ∈ ({-1, 0, 1} : Set ℝ))
    (h₂ : y.2 ∈ ({-1, 0, 1} : Set ℝ)) : ∃ e, repairChildOffset e = y := by
  obtain ⟨y₁, y₂⟩ := y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl
  · exact ⟨(0, 0), by norm_num [repairChildOffset]⟩
  · exact ⟨(0, 1), by norm_num [repairChildOffset]⟩
  · exact ⟨(0, 2), by norm_num [repairChildOffset]⟩
  · exact ⟨(1, 0), by norm_num [repairChildOffset]⟩
  · exact ⟨(1, 1), by norm_num [repairChildOffset]⟩
  · exact ⟨(1, 2), by norm_num [repairChildOffset]⟩
  · exact ⟨(2, 0), by norm_num [repairChildOffset]⟩
  · exact ⟨(2, 1), by norm_num [repairChildOffset]⟩
  · exact ⟨(2, 2), by norm_num [repairChildOffset]⟩

/-- The closed birth of a replacement run is closed.
Auxiliary to area-law Section 11, lines 404–417 and 558–561. -/
theorem isClosed_repairReplacementBirthRegion {ι : Type*} {ξ : ι → Fin 2}
    {σ : RepairFanSlot → ι} (v : ℝ × ℝ) (S : ℝ) (H : RepairFanRun ξ σ) :
    IsClosed (repairReplacementBirthRegion v S ξ σ H) := by
  have : repairReplacementBirthRegion v S ξ σ H =
      ⋃ s : {s : RepairFanSlot // repairFanRunOf ξ σ s = H},
        {w : ℝ × ℝ | w - v ∈ repairFanCone s.val} ∩ Metric.closedBall v (repairHalfSide S) := by
    ext w
    rw [mem_repairReplacementBirthRegion_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs, hw, hn⟩
      exact ⟨⟨s, hs⟩, hw, by simpa [dist_eq_norm] using hn⟩
    · rintro ⟨⟨s, hs⟩, hw, hn⟩
      exact ⟨s, hs, hw, by simpa [dist_eq_norm] using hn⟩
  rw [this]
  exact isClosed_iUnion_of_finite fun s ↦
    (isClosed_repairFanCone_at v s.val).inter Metric.isClosed_closedBall

/-- A point at sup distance `d` from `v` on the ray of a fan direction is the
point `v + d b` of that direction.
Auxiliary to area-law Section 11, lines 404–409 and 497–504. -/
theorem eq_add_smul_of_sameRay {v z : ℝ × ℝ} {d : ℝ} {s : RepairFanSlot}
    (hray : SameRay ℝ (z - v) (repairFanDirection s)) (hn : ‖z - v‖ = d) :
    z = v + d • repairFanDirection s := by
  obtain ⟨t, ht, hzt⟩ := hray.symm.exists_nonneg_left (repairFanDirection_ne_zero s)
  have : t = d := by
    rw [← hn, ← hzt, norm_smul, norm_repairFanDirection, mul_one, Real.norm_of_nonneg ht]
  subst this
  rw [hzt, add_sub_cancel]

private theorem fin_two_ne_one_sub' (x : Fin 2) : x ≠ 1 - x := by
  fin_cases x <;> decide

section Stages

variable {o : ℝ × ℝ} {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)} {C k₀ : ℕ}
  {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

variable {a₀ : ℝ} (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
  (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)
include h

/-- A removal square of a different mark avoids the open square of half-side
`d(S) / 2` about any child of a mark `(v, S)`, and so does a square of half-side
`2 d(S)` about `v`.
Source: area-law Section 11, `geometry:repair-induction`, lines 487–496. -/
theorem RepairMetricHypotheses.disjoint_repairSquare_ball (j : ℕ) {p q : (𝔇 j).markIndex}
    (hpq : p ≠ q) {x : ℝ × ℝ}
    (hx : dist x ((𝔇 j).location p) < 2 * repairHalfSide ((𝔇 j).scale p)) :
    x ∉ repairSquare ((𝔇 j).location q) ((𝔇 j).scale q) := by
  intro hxq
  have hsep := h.separated j p q hpq
  have hdp := h.halfSide_le j p
  have hdq := h.halfSide_le j q
  have hxq' : dist x ((𝔇 j).location q) ≤ repairHalfSide ((𝔇 j).scale q) := hxq
  have htri := dist_triangle ((𝔇 j).location p) x ((𝔇 j).location q)
  rw [dist_comm ((𝔇 j).location p) x] at htri
  set M := max ((𝔇 j).scale p) ((𝔇 j).scale q)
  have hM : 0 < M := (h.scale_pos j p).trans_le (le_max_left _ _)
  have h1 : a₀ / 1000 * (𝔇 j).scale p ≤ a₀ / 1000 * M :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [h.pos])
  have h2 : a₀ / 1000 * (𝔇 j).scale q ≤ a₀ / 1000 * M :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith [h.pos])
  have h3 := mul_pos h.pos hM
  have h4 : a₀ / 1000 * M = a₀ * M / 1000 := by ring
  linarith

/-- **Isolated stars of the next generation.**
Source: area-law Section 11, `geometry:repair-induction`, lines 486–514. -/
theorem RepairMetricHypotheses.isIsolatedStar_succ (ha₀ : a₀ ≤ 1 / 4) (j : ℕ)
    (hstar : ∀ p, IsIsolatedStar (𝔇 j).current (𝔇 j).color ((𝔇 j).location p)
      (a₀ * (𝔇 j).scale p)) (q : (𝔇 (j + 1)).markIndex) :
    IsIsolatedStar (𝔇 (j + 1)).current (𝔇 (j + 1)).color ((𝔇 (j + 1)).location q)
      (a₀ * (𝔇 (j + 1)).scale q) := by
  set D := 𝔇 j with hD
  let : Nonempty D.regionIndex := ⟨D.dummy⟩
  set σR := repairCurrentAssignments D.current D.location D.scale with hσR_def
  revert q
  rintro ⟨⟨n, hn⟩, ⟨p, hp⟩, e⟩
  subst hn
  set v := D.location p
  set d := repairHalfSide (D.scale p) with hd_def
  have hd : 0 < d := repairHalfSide_pos _
  have hS := h.scale_pos j p
  have hdS := h.halfSide_le j p
  have hr : 0 < a₀ * D.scale p := mul_pos h.pos hS
  have h6 : 6 * d ≤ a₀ * D.scale p := by nlinarith
  obtain ⟨σ, hcl, hint, hcol, hsub⟩ := (hstar p).exists_model hr
  have hσ : σR p = σ := funext fun s ↦
    repairCurrentSectorAssignment_eq (by positivity) h6 hcl hsub s
  subst hσ
  change IsIsolatedStar (𝔇 (j + 1)).current (𝔇 (j + 1)).color
    (v + d • repairChildOffset e) (a₀ * d)
  have hball : ∀ x ∈ Metric.ball (v + d • repairChildOffset e) (d / 2), dist x v < 2 * d := by
    intro x hx
    rw [Metric.mem_ball] at hx
    have h1 : dist (v + d • repairChildOffset e) v ≤ d := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hd.le]
      exact mul_le_of_le_one_right hd.le (norm_repairChildOffset_le e)
    linarith [dist_triangle x (v + d • repairChildOffset e) v]
  refine isIsolatedStar_repairChild (by nlinarith) hcl hint hcol (𝔇 (j + 1)).current
    (𝔇 (j + 1)).color (fun i ↦ (Sum.inl i : (𝔇 (j + 1)).regionIndex))
    (fun H ↦ (Sum.inr (⟨j + 1, rfl⟩, ⟨⟨p, hp⟩, H⟩) : (𝔇 (j + 1)).regionIndex))
    Sum.inl_injective ?_ (fun i H ↦ Sum.inl_ne_inr) e ?_ ?_ ?_ ?_
    ?_ (mul_pos h.pos hd) (by nlinarith)
  · intro H H' hH
    exact eq_of_heq (Sigma.mk.inj (Prod.mk.inj (Sum.inr.inj hH)).2).2
  · intro i
    ext x
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨hxR, hxU⟩, hxN⟩
      exact ⟨⟨hxR, fun hxQ ↦ hxU (Set.mem_iUnion.mpr ⟨p, hxQ⟩)⟩, hxN⟩
    · rintro ⟨⟨hxR, hxQ⟩, hxN⟩
      refine ⟨⟨hxR, fun hxU ↦ ?_⟩, hxN⟩
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hxU
      by_cases hpq : p = q
      · subst hpq
        exact hxQ hq
      · exact h.disjoint_repairSquare_ball j hpq (hball x hxN) hq
  · intro H
    rfl
  · intro x hx₁ hx₂
    rcases x with i | ⟨⟨n', hn'⟩, ⟨p', hp'⟩, H⟩
    · exact absurd rfl (hx₁ i)
    subst hn'
    by_cases hpp : p' = p
    · subst hpp
      exact absurd rfl (hx₂ H)
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzN⟩
    have hsq : closure ((𝔇 (j + 1)).current (Sum.inr (⟨j + 1, rfl⟩, ⟨⟨p', hp'⟩, H⟩))) ⊆
        repairSquare (D.location p') (D.scale p') := by
      apply closure_minimal _ Metric.isClosed_closedBall
      exact interior_subset.trans (repairReplacementBirthRegion_subset_repairSquare _ _ _ _ H)
    exact h.disjoint_repairSquare_ball j (Ne.symm hpp) (hball z hzN) (hsq hz)
  · intro i
    rfl
  · intro H
    rfl

/-- **Same-label contacts of a replacement.** A replacement meets a distinct
identifier of the same label only at marks of the next generation.
Source: area-law Section 11, `geometry:repair-induction`, lines 479–482 and
497–504. -/
theorem RepairMetricHypotheses.contact_subset_marks (j : ℕ)
    (hstar : ∀ p, IsIsolatedStar (𝔇 j).current (𝔇 j).color ((𝔇 j).location p)
      (a₀ * (𝔇 j).scale p))
    (x y : (𝔇 (j + 1)).regionIndex) (m : (𝔇 j).markIndex) (hxy : x ≠ y)
    (hpar : repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m)
    (hcol : (𝔇 (j + 1)).color x = (𝔇 (j + 1)).color y) :
    closure ((𝔇 (j + 1)).current x) ∩ closure ((𝔇 (j + 1)).current y) ⊆
      Set.range (𝔇 (j + 1)).location := by
  set D := 𝔇 j with hD
  let : Nonempty D.regionIndex := ⟨D.dummy⟩
  set σR := repairCurrentAssignments D.current D.location D.scale with hσR_def
  rintro z ⟨hzx, hzy⟩
  rcases x with i | ⟨⟨n, hn⟩, ⟨p, hp⟩, H⟩
  · cases hpar
  subst hn
  set v := D.location p
  set d := repairHalfSide (D.scale p) with hd_def
  have hd : 0 < d := repairHalfSide_pos _
  have hS := h.scale_pos j p
  have hdS := h.halfSide_le j p
  have hr : 0 < a₀ * D.scale p := mul_pos h.pos hS
  have h6 : 6 * d ≤ a₀ * D.scale p := by nlinarith [h.le_one]
  obtain ⟨σ, hcl, -, hcolσ, hsub⟩ := (hstar p).exists_model hr
  have hσ : σR p = σ := funext fun s ↦
    repairCurrentSectorAssignment_eq (by positivity) h6 hcl hsub s
  -- The replacement side.
  have hzT : z ∈ repairReplacementBirthRegion v (D.scale p) D.color (σR p) H :=
    closure_minimal interior_subset (isClosed_repairReplacementBirthRegion _ _ H) hzx
  obtain ⟨u, hu, hzu, hzd⟩ := (mem_repairReplacementBirthRegion_iff H).mp hzT
  have hcolx : (𝔇 (j + 1)).color (Sum.inr (⟨j + 1, rfl⟩, ⟨⟨p, hp⟩, H⟩)) =
      1 - D.color (σR p u) := by
    rw [← hu]
    rfl
  -- A mark at `v + d b` for a fan direction `b`.
  have hmark : ∀ w : RepairFanSlot, z = v + d • repairFanDirection w →
      z ∈ Set.range (𝔇 (j + 1)).location := by
    intro w hz
    obtain ⟨e, he⟩ := exists_repairChildOffset_eq (repairFanDirection_mem w).2.1
      (repairFanDirection_mem w).2.2
    refine ⟨(⟨j + 1, rfl⟩, (⟨p, hp⟩, e)), ?_⟩
    rw [hz, ← he]
    rfl
  have hcenter : z = v → z ∈ Set.range (𝔇 (j + 1)).location := by
    intro hz
    refine ⟨(⟨j + 1, rfl⟩, (⟨p, hp⟩, (1, 1))), ?_⟩
    rw [hz]
    change v + d • repairChildOffset (1, 1) = v
    simp [repairChildOffset]
  rcases y with i | ⟨⟨n', hn'⟩, ⟨p', hp'⟩, H'⟩
  · -- An old remnant.
    have hzQ : d ≤ ‖z - v‖ := by
      have hsub' : D.current i \ repairRemovalSet D.location D.scale ⊆
          (Metric.closedBall v d)ᶜ := by
        rintro w ⟨-, hw⟩ hwQ
        exact hw (Set.mem_iUnion.mpr ⟨p, hwQ⟩)
      have := closure_mono hsub' hzy
      rw [closure_compl, interior_closedBall v hd.ne'] at this
      simpa [dist_eq_norm] using this
    have hzn : ‖z - v‖ = d := le_antisymm hzd hzQ
    have hzR : z ∈ closure (D.current i) := closure_mono Set.sdiff_subset hzy
    have hzb : z ∈ Metric.ball v (a₀ * D.scale p) := by
      rw [Metric.mem_ball, dist_eq_norm, hzn]
      linarith
    obtain ⟨⟨s, hs, hzs⟩, -⟩ := (hcl i).subset ⟨hzR, hzb⟩
    have hcoly : (𝔇 (j + 1)).color (Sum.inl i) = D.color i := rfl
    rw [hcolx, hcoly, ← hs, hσ] at hcol
    have hus : u ≠ s := by
      rintro rfl
      exact fin_two_ne_one_sub' _ hcol.symm
    have hz0 : z - v ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hzn
      linarith
    by_cases h₁ : s = cellFanNext u
    · subst h₁
      exact hmark u (eq_add_smul_of_sameRay
        ((mem_repairFanCone_inter_next_iff u _).mp ⟨hzu, hzs⟩) hzn)
    by_cases h₂ : u = cellFanNext s
    · subst h₂
      exact hmark s (eq_add_smul_of_sameRay
        ((mem_repairFanCone_inter_next_iff s _).mp ⟨hzs, hzu⟩) hzn)
    exact absurd (eq_zero_of_mem_repairFanCone hus h₁ h₂ hzu hzs) hz0
  · subst hn'
    by_cases hpp : p' = p
    · -- A peer replacement of the same parent.
      subst hpp
      have hHH : H ≠ H' := fun h ↦ hxy (by rw [h])
      have hzT' : z ∈ repairReplacementBirthRegion v (D.scale p') D.color (σR p') H' :=
        closure_minimal interior_subset (isClosed_repairReplacementBirthRegion _ _ H') hzy
      obtain ⟨u', hu', hzu', -⟩ := (mem_repairReplacementBirthRegion_iff H').mp hzT'
      have hcoly : (𝔇 (j + 1)).color (Sum.inr (⟨j + 1, rfl⟩, ⟨⟨p', hp'⟩, H'⟩)) =
          1 - D.color (σR p' u') := by
        rw [← hu']
        rfl
      rw [hcolx, hcoly, sub_right_inj] at hcol
      have huu : u ≠ u' := by
        rintro rfl
        exact hHH (hu.symm.trans hu')
      by_cases h₁ : u' = cellFanNext u
      · subst h₁
        exact absurd (hu.symm.trans (((repairFanRunOf_next_eq_iff _ _ u).mpr hcol).trans hu'))
          hHH
      by_cases h₂ : u = cellFanNext u'
      · subst h₂
        exact absurd (hu.symm.trans (((repairFanRunOf_next_eq_iff _ _ u').mpr
          hcol.symm).symm.trans hu')) hHH
      exact hcenter (sub_eq_zero.mp (eq_zero_of_mem_repairFanCone huu h₁ h₂ hzu hzu'))
    · -- A replacement of another parent.
      have hzT' : z ∈ repairSquare (D.location p') (D.scale p') :=
        closure_minimal (interior_subset.trans
          (repairReplacementBirthRegion_subset_repairSquare _ _ _ _ H'))
          Metric.isClosed_closedBall hzy
      have hzP : z ∈ repairSquare v (D.scale p) :=
        repairReplacementBirthRegion_subset_repairSquare _ _ _ _ H hzT
      exact absurd hzT' (Set.disjoint_left.mp (h.disjoint_repairSquare j p p'
        (Ne.symm hpp)) hzP)

end Stages

end TNLean.PEPS.AreaLaw.Geometry
