/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationReplacement
import TNLean.PEPS.AreaLaw.Geometry.IsolatedStars
import TNLean.PEPS.AreaLaw.Geometry.FanRegularity

/-!
# Same-label regions near a replacement, from an isolated star

Let the closed square of half-side `ρ` about a mark `v` be an isolated star of
a labelled region family, and let `u > 0` with `6u ≤ ρ`. The working-wedge
assignment of the repair, read in the triangles of half-side `6u`, agrees with
the assignment of the star: the interior of a fan triangle meets no other fan
triangle of the same half-side.

Consequently every point of a region `R i` within sup distance `2u` of `v`
but outside the closed square of half-side `u` lies, after normalization by
`u`, in the exterior trapezoid of a wedge assigned to `i`. When the label of
`i` is opposite to the exterior label of a run `C` of that assignment, this
point lies in the same-label bound of `C`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:initial-stars`, lines 332–349;
replacement instructions, lines 393–417; `geometry:repair-induction`,
lines 486–494; and `geometry:birth-separation`, lines 584–615.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

/-! ### Normalized triangles -/

/-- Inside the closed triangle of a wedge, the maximum norm is the outer
coordinate.
Source: area-law Section 11, lines 404–417. -/
theorem norm_le_outer_of_mem_repairNormTriangle {L : ℤ} {s : RepairFanSlot} {x : ℝ × ℝ}
    (hx : x ∈ repairNormTriangle L s) :
    ‖x‖ ≤ ((repairSlotFacets s).1.1 : ℝ) * x.1 + (repairSlotFacets s).1.2 * x.2 := by
  obtain ⟨⟨-, h₂⟩, h₃⟩ := hx
  rcases s with ⟨k, j⟩
  simp only [intHalfPlane, Set.mem_ofPred_eq] at h₂ h₃
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff, abs_le, abs_le]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    fin_cases k <;> fin_cases j <;> simp only [repairSlotFacets] at h₂ h₃ ⊢ <;>
    push_cast at h₂ h₃ ⊢ <;> linarith

/-- Doubling maps the elementary triangle onto the doubled triangle. -/
theorem two_smul_mem_repairNormTriangle {s : RepairFanSlot} {x : ℝ × ℝ}
    (hx : x ∈ repairNormTriangle 1 s) : (2 : ℝ) • x ∈ repairNormTriangle 2 s := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hx
  simp only [repairNormTriangle, intHalfPlane, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h₁ h₂ h₃ ⊢
  push_cast at h₁ h₂ h₃ ⊢
  refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- An interior point of the elementary triangle satisfies both radial facet
inequalities strictly. -/
private theorem interior_repairNormTriangle_strict {s : RepairFanSlot} {x : ℝ × ℝ}
    (hx : x ∈ interior (repairNormTriangle 1 s)) :
    ((repairSlotFacets s).2.1.1 : ℝ) * x.1 + (repairSlotFacets s).2.1.2 * x.2 < 0 ∧
      ((repairSlotFacets s).2.2.1 : ℝ) * x.1 + (repairSlotFacets s).2.2.2 * x.2 < 0 := by
  have key : ∀ a b : ℤ, (a, b) ≠ (0, 0) → interior (repairNormTriangle 1 s) ⊆ intHalfPlane a b 0 →
      (a : ℝ) * x.1 + b * x.2 < 0 := by
    intro a b hab hsub
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    have hab' : (0 : ℝ) < (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
      rcases ne_or_eq a 0 with ha | ha
      · have : (a : ℝ) ≠ 0 := by exact_mod_cast ha
        positivity
      · have hb : b ≠ 0 := fun hb ↦ hab (by rw [ha, hb])
        have : (b : ℝ) ≠ 0 := by exact_mod_cast hb
        positivity
    set t := ε / (2 * (|(a : ℝ)| + |(b : ℝ)| + 1))
    have ht : 0 < t := by positivity
    have hmem : x + t • ((a : ℝ), (b : ℝ)) ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
      have hn : ‖((a : ℝ), (b : ℝ))‖ ≤ |(a : ℝ)| + |(b : ℝ)| + 1 := by
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
        exact max_le (by linarith [abs_nonneg (b : ℝ)]) (by linarith [abs_nonneg (a : ℝ)])
      have hpos : 0 < |(a : ℝ)| + |(b : ℝ)| + 1 := by positivity
      calc t * ‖((a : ℝ), (b : ℝ))‖ ≤ t * (|(a : ℝ)| + |(b : ℝ)| + 1) :=
            mul_le_mul_of_nonneg_left hn ht.le
        _ = ε / 2 := by simp only [t]; field_simp
        _ < ε := by linarith
    have := hsub (hball hmem)
    simp only [intHalfPlane, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, Int.cast_zero] at this
    nlinarith
  have h₂ : interior (repairNormTriangle 1 s) ⊆
      intHalfPlane (repairSlotFacets s).2.1.1 (repairSlotFacets s).2.1.2 0 :=
    interior_subset.trans fun _ h ↦ h.1.2
  have h₃ : interior (repairNormTriangle 1 s) ⊆
      intHalfPlane (repairSlotFacets s).2.2.1 (repairSlotFacets s).2.2.2 0 :=
    interior_subset.trans fun _ h ↦ h.2
  rcases s with ⟨k, j⟩
  constructor
  · exact key _ _ (by fin_cases k <;> fin_cases j <;> decide) h₂
  · exact key _ _ (by fin_cases k <;> fin_cases j <;> decide) h₃

/-- The interior of an elementary triangle meets no other elementary triangle.
Source: area-law Section 11, lines 404–417. -/
theorem interior_repairNormTriangle_inter_eq_empty {s t : RepairFanSlot} (hst : s ≠ t) :
    interior (repairNormTriangle 1 s) ∩ repairNormTriangle 1 t = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨hx, hy⟩ ↦ ?_
  obtain ⟨h₂, h₃⟩ := interior_repairNormTriangle_strict hx
  obtain ⟨⟨-, g₂⟩, g₃⟩ := hy
  rcases s with ⟨k, a⟩
  rcases t with ⟨l, b⟩
  simp only [intHalfPlane, Set.mem_ofPred_eq] at g₂ g₃
  fin_cases k <;> fin_cases a <;> fin_cases l <;> fin_cases b <;>
    simp [repairSlotFacets] at hst h₂ h₃ g₂ g₃ <;> linarith

/-! ### Actual fan triangles about a mark -/

/-- The affine homeomorphism `x ↦ v + r x` for `r ≠ 0`. -/
private def scaleHomeomorph (v : ℝ × ℝ) {r : ℝ} (hr : r ≠ 0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addLeft v)

private theorem repairCurrentFanTriangle_eq_image (v : ℝ × ℝ) {r : ℝ} (hr : r ≠ 0)
    (s : RepairFanSlot) :
    repairCurrentFanTriangle v r s =
      scaleHomeomorph v hr '' (cellFanPolygon (-1, -1) 1 (0, 0) repairFanSplit s).region :=
  rfl

/-- The interior of an actual fan triangle about `v` meets no other fan
triangle of the same half-side.
Source: area-law Section 11, `geometry:initial-stars`, lines 340–349. -/
theorem interior_repairCurrentFanTriangle_inter_eq_empty (v : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    {s t : RepairFanSlot} (hst : s ≠ t) :
    interior (repairCurrentFanTriangle v r s) ∩ repairCurrentFanTriangle v r t = ∅ := by
  rw [repairCurrentFanTriangle_eq_image v hr.ne', repairCurrentFanTriangle_eq_image v hr.ne',
    ← (scaleHomeomorph v hr.ne').image_interior,
    ← Set.image_inter (scaleHomeomorph v hr.ne').injective, Set.image_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨hx, hy⟩ ↦ ?_
  have := interior_repairNormTriangle_inter_eq_empty hst
  exact this.subset ⟨interior_mono (cellFanPolygon_region_subset_repairNormTriangle s) hx,
    cellFanPolygon_region_subset_repairNormTriangle t hy⟩

theorem interior_repairCurrentFanTriangle_nonempty (v : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (s : RepairFanSlot) : (interior (repairCurrentFanTriangle v r s)).Nonempty := by
  rw [repairCurrentFanTriangle_eq_image v hr.ne', ← (scaleHomeomorph v hr.ne').image_interior]
  exact (cellFanPolygon_interior_nonempty_and_closure_eq _ _ _ _ s).1.image _

theorem repairCurrentFanTriangle_subset_closedBall (v : ℝ × ℝ) {r : ℝ} (hr : 0 < r)
    (s : RepairFanSlot) : repairCurrentFanTriangle v r s ⊆ Metric.closedBall v r := by
  rw [← repairCurrentFanTriangle_inter_closedBall v hr le_rfl s]
  exact Set.inter_subset_right

/-! ### The working-wedge assignment in an isolated star -/

/-- **The repair assignment agrees with the star.** In an isolated star of
half-side `ρ`, the identifier chosen for each working wedge of half-side
`r ≤ ρ` is the identifier assigned to that wedge by the star.
Source: area-law Section 11, `geometry:initial-stars`, lines 332–349, and
`geometry:repair-induction`, lines 486–494. -/
theorem IsIsolatedStar.exists_repairCurrentSectorAssignment_eq {ι : Type*} [Nonempty ι]
    {R : ι → Set (ℝ × ℝ)} {ξ : ι → Fin 2} {v : ℝ × ℝ} {ρ r : ℝ}
    (h : IsIsolatedStar R ξ v ρ) (hr : 0 < r) (hrρ : r ≤ ρ) :
    ∃ σ' : RepairFanSlot → ι,
      (∀ i, closure (R i) ∩ Metric.closedBall v ρ =
        ⋃ s : {s : RepairFanSlot // σ' s = i}, repairCurrentFanTriangle v ρ s.val) ∧
      ∀ s, repairCurrentSectorAssignment R v r s = σ' s := by
  obtain ⟨σ', hsub, hdecomp, -, -, -⟩ := h
  refine ⟨σ', hdecomp, fun s ↦ ?_⟩
  have hmono : repairCurrentFanTriangle v r s ⊆ repairCurrentFanTriangle v ρ s := by
    rw [← repairCurrentFanTriangle_inter_closedBall v hr hrρ s]
    exact Set.inter_subset_left
  have hP : interior (repairCurrentFanTriangle v r s) ⊆ R (σ' s) :=
    (interior_mono hmono).trans (hsub s)
  have hspec : interior (repairCurrentFanTriangle v r s) ⊆
      R (repairCurrentSectorAssignment R v r s) :=
    Classical.epsilon_spec (p := fun i ↦ interior (repairCurrentFanTriangle v r s) ⊆ R i)
      ⟨σ' s, hP⟩
  obtain ⟨z, hz⟩ := interior_repairCurrentFanTriangle_nonempty v hr s
  have hzb : z ∈ Metric.closedBall v ρ :=
    Metric.closedBall_subset_closedBall hrρ
      (repairCurrentFanTriangle_subset_closedBall v hr s (interior_subset hz))
  have hzc : z ∈ closure (R (repairCurrentSectorAssignment R v r s)) ∩
      Metric.closedBall v ρ := ⟨subset_closure (hspec hz), hzb⟩
  rw [hdecomp] at hzc
  obtain ⟨⟨t, ht⟩, hzt⟩ := Set.mem_iUnion.mp hzc
  by_cases hst : s = t
  · subst hst; exact ht.symm
  · have hρ : 0 < ρ := hr.trans_le hrρ
    have := interior_repairCurrentFanTriangle_inter_eq_empty v hρ hst
    exact (this.subset ⟨interior_mono hmono hz, hzt⟩).elim

/-- **Local bound from an isolated star.** In an isolated star of half-side
`ρ ≥ 6u`, a point of a region `R i` at sup distance in `(u, 2u)` from the mark
lies, after normalization by `u`, in the exterior trapezoid of a working wedge
whose repair assignment is `i`.
Source: area-law Section 11, `geometry:initial-stars`, lines 332–349, and
`geometry:birth-separation`, lines 584–615. -/
theorem IsIsolatedStar.exists_mem_repairExteriorTrapezoid {ι : Type*} [Nonempty ι]
    {R : ι → Set (ℝ × ℝ)} {ξ : ι → Fin 2} {v : ℝ × ℝ} {ρ u : ℝ}
    (h : IsIsolatedStar R ξ v ρ) (hu : 0 < u) (h6 : 6 * u ≤ ρ) {i : ι} {w : ℝ × ℝ}
    (hw : w ∈ R i) (hnear : ‖w - v‖ < 2 * u) (hout : u < ‖w - v‖) :
    ∃ t, repairCurrentSectorAssignment R v (6 * u) t = i ∧
      u⁻¹ • (w - v) ∈ repairExteriorTrapezoid t := by
  obtain ⟨σ', hdecomp, heq⟩ := h.exists_repairCurrentSectorAssignment_eq (by positivity) h6
  have hρ : 0 < ρ := by linarith
  have hwb : w ∈ closure (R i) ∩ Metric.closedBall v ρ :=
    ⟨subset_closure hw, by rw [Metric.mem_closedBall, dist_eq_norm]; linarith⟩
  rw [hdecomp] at hwb
  obtain ⟨⟨t, ht⟩, hwt⟩ := Set.mem_iUnion.mp hwb
  refine ⟨t, (heq t).trans ht, ?_⟩
  have hw2 : w ∈ repairCurrentFanTriangle v (2 * u) t := by
    rw [← repairCurrentFanTriangle_inter_closedBall v (ρ' := 2 * u) (ρ := ρ) (by positivity)
      (by linarith) t]
    exact ⟨hwt, by rw [Metric.mem_closedBall, dist_eq_norm]; linarith⟩
  obtain ⟨x, hx, rfl⟩ := hw2
  dsimp only at hout
  have hxT := cellFanPolygon_region_subset_repairNormTriangle t hx
  have hval : u⁻¹ • (v + (2 * u) • x - v) = (2 : ℝ) • x := by
    rw [add_sub_cancel_left, smul_smul]
    congr 1
    field_simp
  rw [hval]
  have h2 := two_smul_mem_repairNormTriangle hxT
  refine ⟨h2, ?_⟩
  have hn := norm_le_outer_of_mem_repairNormTriangle h2
  have hnorm : 1 < ‖(2 : ℝ) • x‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity)] at hout
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  simp only [intHalfPlane, Set.mem_ofPred_eq, Int.cast_neg, Int.cast_one] at hn ⊢
  linarith

end TNLean.PEPS.AreaLaw.Geometry
