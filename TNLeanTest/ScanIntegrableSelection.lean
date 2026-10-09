/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.EntropyBalance
import TNLean.PEPS.AreaLaw.Scan.Selection

/-!
# Integrable, discontinuous scan selection regressions

The scalar defect below equals the identity except at `0` and `1/2`, where it equals `1`.
It is bounded and strictly positive on `[0, 1]`, but has no minimum there and is discontinuous
even on `(0, 1)`. Its interval integral is exactly `1/2`. Thus neither the exact averaging
regression nor the two-round derivative telescope can use the former continuity hypotheses.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open TNLean.PEPS.AreaLaw.Scan

namespace TNLeanTest.ScanIntegrableSelection

noncomputable section

/-- Two upward point modifications of the identity, including one in the interval's interior. -/
def discontinuousDefect (p : ℝ) : ℝ :=
  if p = 0 ∨ p = 1 / 2 then 1 else p

/-- Away from the two exceptional points the defect is the original identity. -/
theorem discontinuousDefect_eq {p : ℝ} (hzero : p ≠ 0) (hhalf : p ≠ 1 / 2) :
    discontinuousDefect p = p :=
  ite_eq_right (not_or.mpr ⟨hzero, hhalf⟩)

/-- The original pointwise defect, including its exceptional values, lies in `(0, 1]`. -/
theorem discontinuousDefect_bounded {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    0 < discontinuousDefect p ∧ discontinuousDefect p ≤ 1 := by
  unfold discontinuousDefect
  split_ifs with h
  · norm_num
  · have hzero : p ≠ 0 := fun hpzero ↦ h (Or.inl hpzero)
    exact ⟨lt_of_le_of_ne hp.1 hzero.symm, hp.2⟩

/-- Every value has a strictly smaller value on the same closed interval. -/
theorem discontinuousDefect_exists_lt {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ∃ q ∈ Icc (0 : ℝ) 1, discontinuousDefect q < discontinuousDefect p := by
  obtain ⟨hpos, hle⟩ := discontinuousDefect_bounded hp
  have hzero : discontinuousDefect p / 3 ≠ 0 := ne_of_gt (by positivity)
  have hhalf : discontinuousDefect p / 3 ≠ 1 / 2 := ne_of_lt (by linarith)
  refine ⟨discontinuousDefect p / 3, ⟨by positivity, by linarith⟩, ?_⟩
  rw [discontinuousDefect_eq hzero hhalf]
  linarith

/-- Compactness cannot supply a minimizing point for this bounded integrable function. -/
theorem discontinuousDefect_no_minimum :
    ¬ ∃ p ∈ Icc (0 : ℝ) 1, IsMinOn discontinuousDefect (Icc 0 1) p := by
  rintro ⟨p, hp, hmin⟩
  obtain ⟨q, hq, hlt⟩ := discontinuousDefect_exists_lt hp
  exact hlt.not_ge (hmin hq)

/-- In particular the closed-interval continuity premise of the old selector is false. -/
theorem discontinuousDefect_not_continuousOn_Icc :
    ¬ ContinuousOn discontinuousDefect (Icc (0 : ℝ) 1) := by
  intro hcont
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hcont
  exact discontinuousDefect_no_minimum ⟨p, hp, hmin⟩

/-- Changing two points preserves the Lebesgue almost-everywhere identity. -/
theorem discontinuousDefect_ae_eq_id :
    discontinuousDefect =ᵐ[volume] fun p : ℝ ↦ p := by
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (1 / 2 : ℝ)] with p hzero hhalf
  exact discontinuousDefect_eq hzero hhalf

/-- The weakened telescope premise holds on the entire open parameter interval. -/
theorem discontinuousDefect_aestronglyMeasurable :
    AEStronglyMeasurable discontinuousDefect (volume.restrict (Ioo (0 : ℝ) 1)) :=
  continuous_id.aestronglyMeasurable.congr
    (ae_restrict_of_ae discontinuousDefect_ae_eq_id.symm)

/-- The interior modification prevents even open-interval continuity. -/
theorem discontinuousDefect_not_continuousOn_Ioo :
    ¬ ContinuousOn discontinuousDefect (Ioo (0 : ℝ) 1) := by
  intro hcont
  have heq := volume.eqOn_Ioo_of_ae_eq (ae_restrict_of_ae discontinuousDefect_ae_eq_id)
    hcont continuous_id.continuousOn
  have hhalf := heq (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num)
  norm_num [discontinuousDefect] at hhalf

/-- Integrability belongs to the actual pointwise defect, not merely to a replacement function. -/
theorem discontinuousDefect_intervalIntegrable :
    IntervalIntegrable discontinuousDefect volume 0 1 :=
  (continuous_id.intervalIntegrable 0 1).congr_ae
    (ae_restrict_of_ae discontinuousDefect_ae_eq_id.symm)

/-- The exact integral is unchanged by the two point modifications. -/
theorem discontinuousDefect_integral :
    (∫ p in (0 : ℝ)..1, discontinuousDefect p) = 1 / 2 := by
  calc
    (∫ p in (0 : ℝ)..1, discontinuousDefect p) = ∫ p in (0 : ℝ)..1, p :=
      intervalIntegral.integral_congr_ae_restrict
        (ae_restrict_of_ae discontinuousDefect_ae_eq_id)
    _ = 1 / 2 := by norm_num

/-- The integral hypothesis is proved at the exact threshold, with no positive slack. -/
theorem discontinuousDefect_integral_le :
    (∫ p in (0 : ℝ)..1, discontinuousDefect p) ≤ 1 / 2 :=
  discontinuousDefect_integral.le

/-- Exact finite averaging selects a point even though neither function attains a minimum. -/
theorem discontinuousDefect_exact_selection :
    ∃ r ∈ (Finset.univ : Finset (Fin 2)),
      ∃ p ∈ Icc (0 : ℝ) 1, (fun _ : Fin 2 ↦ discontinuousDefect) r p ≤ 1 / 2 := by
  apply exists_mem_Icc_le_of_sum_integral_le (fun _ : Fin 2 ↦ discontinuousDefect)
    Finset.univ (by simp) (by norm_num : (0 : ℝ) < 1)
    (fun _ _ ↦ discontinuousDefect_intervalIntegrable)
  norm_num [discontinuousDefect_integral]

/-- Two affine entropy rounds telescope with a pointwise gain bound and the discontinuous defect.
The adjacent values agree exactly; the gain derivative is `1` even at the exceptional
interior point. -/
theorem discontinuousDefect_telescope :
    (∑ _r : Fin 2, ∫ p in (0 : ℝ)..1, discontinuousDefect p) ≤ 2 := by
  have h := sum_integral_le_of_deriv
    (fun (r : Fin 2) (p : ℝ) ↦ -(r.val : ℝ) - p)
    (fun _ : Fin 2 ↦ discontinuousDefect) Finset.univ
    (coef := 1) (err := 0) (α := 0) (β := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ ↦ (continuous_const.sub continuous_id).continuousOn)
    (fun r ↦ ((differentiable_const (-(r.val : ℝ))).sub differentiable_id).differentiableOn)
    (fun _ p hp ↦ (discontinuousDefect_bounded ⟨hp.1.le, hp.2.le⟩).1.le)
    (fun _ ↦ discontinuousDefect_aestronglyMeasurable)
    ⟨1, fun _ p hp ↦ (discontinuousDefect_bounded ⟨hp.1.le, hp.2.le⟩).2⟩
    (by
      intro r _ p hp
      simpa only [one_mul, sub_zero, deriv_const_sub_id, neg_neg] using
        (discontinuousDefect_bounded ⟨hp.1.le, hp.2.le⟩).2)
    (by
      intro r p _
      norm_num [deriv_const_sub_id])
    (by
      intro r _
      push_cast
      ring)
  simp at h
  rw [Fin.sum_univ_two]
  linarith

end

end TNLeanTest.ScanIntegrableSelection
