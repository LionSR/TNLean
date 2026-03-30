/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Overlap.Basic
import TNLean.Analysis.ConvergenceHelpers

/-!
# MPS-specific convergence helpers for MPV overlap arguments

MPS-specific convergence lemmas used in the fundamental theorem proof chain.
The general-purpose convergence lemmas (`bounded_mul_tendsto_zero`,
`geometric_mul_bounded_tendsto_zero`, `sum_tendsto_one_of_diag`) live in
`TNLean.Analysis.ConvergenceHelpers`.

## Main results

- `tendsto_inner_zero`: mpvOverlap → 0 implies mpvInner → 0
- `tendsto_inner_one`: mpvOverlap → 1 (self) implies mpvInner → 1
- `geometric_mul_inner_tendsto_zero`: geometric(< 1) × Cauchy-Schwarz-bounded inner → 0
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

variable {d : ℕ}

/-- `mpvOverlap → 0` implies `mpvInner → 0`, via the relation
`mpvOverlap = star ∘ mpvInner`. -/
lemma tendsto_inner_zero {D₁ D₂ : ℕ} (X : MPSTensor d D₁) (Y : MPSTensor d D₂)
    (hOv : Tendsto (fun N => mpvOverlap (d := d) X Y N) atTop (nhds 0)) :
    Tendsto (fun N => mpvInner (d := d) X Y N) atTop (nhds 0) := by
  simpa [mpvOverlap_eq_star_mpvInner] using hOv.star

/-- `mpvOverlap X X → 1` (self-overlap) implies `mpvInner X X → 1`, via the relation
`mpvOverlap = star ∘ mpvInner`. -/
lemma tendsto_inner_one {D : ℕ} (X : MPSTensor d D)
    (hOv : Tendsto (fun N => mpvOverlap (d := d) X X N) atTop (nhds 1)) :
    Tendsto (fun N => mpvInner (d := d) X X N) atTop (nhds 1) := by
  simpa [mpvOverlap_eq_star_mpvInner] using hOv.star

/-- Geometric factor with `‖c‖ < 1` times a Cauchy-Schwarz-bounded inner product tends to
zero, given that both self-overlaps converge to 1. -/
lemma geometric_mul_inner_tendsto_zero {D₁ D₂ : ℕ} (c : ℂ)
    (X : MPSTensor d D₁) (Y : MPSTensor d D₂) (hc : ‖c‖ < 1)
    (hX : Tendsto (fun N => mpvOverlap (d := d) X X N) atTop (nhds 1))
    (hY : Tendsto (fun N => mpvOverlap (d := d) Y Y N) atTop (nhds 1)) :
    Tendsto (fun N => c ^ N * mpvInner (d := d) X Y N) atTop (nhds 0) := by
  have hX_inner : Tendsto (fun N => mpvInner (d := d) X X N) atTop (nhds 1) :=
    tendsto_inner_one X hX
  have hY_inner : Tendsto (fun N => mpvInner (d := d) Y Y N) atTop (nhds 1) :=
    tendsto_inner_one Y hY
  obtain ⟨C_X, hC_X⟩ :=
    (Metric.isBounded_range_of_tendsto _ hX_inner).exists_norm_le
  obtain ⟨C_Y, hC_Y⟩ :=
    (Metric.isBounded_range_of_tendsto _ hY_inner).exists_norm_le
  have hXX_bdd : ∀ N, ‖mpvInner (d := d) X X N‖ ≤ C_X :=
    fun N => hC_X _ (Set.mem_range_self N)
  have hYY_bdd : ∀ N, ‖mpvInner (d := d) Y Y N‖ ≤ C_Y :=
    fun N => hC_Y _ (Set.mem_range_self N)
  -- ‖mpvState X N‖² = ‖mpvInner X X N‖ via inner_self_eq_norm_sq_to_K.
  have hXX_sq : ∀ N,
      ‖mpvState (d := d) X N‖ ^ 2 = ‖mpvInner (d := d) X X N‖ := fun N => by
    have heq : mpvInner (d := d) X X N = ↑(‖mpvState (d := d) X N‖ ^ 2 : ℝ) := by
      unfold mpvInner
      rw [inner_self_eq_norm_sq_to_K]
      push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hYY_sq : ∀ N,
      ‖mpvState (d := d) Y N‖ ^ 2 = ‖mpvInner (d := d) Y Y N‖ := fun N => by
    have heq : mpvInner (d := d) Y Y N = ↑(‖mpvState (d := d) Y N‖ ^ 2 : ℝ) := by
      unfold mpvInner
      rw [inner_self_eq_norm_sq_to_K]
      push_cast; rfl
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  -- Cauchy-Schwarz + AM-GM gives ‖mpvInner X Y N‖ ≤ (C_X + C_Y) / 2.
  apply geometric_mul_bounded_tendsto_zero c _ ((C_X + C_Y) / 2) hc
  intro N
  have h_cs : ‖mpvInner (d := d) X Y N‖ ≤
      ‖mpvState (d := d) X N‖ * ‖mpvState (d := d) Y N‖ := by
    unfold mpvInner; exact norm_inner_le_norm _ _
  calc ‖mpvInner (d := d) X Y N‖
      ≤ ‖mpvState (d := d) X N‖ * ‖mpvState (d := d) Y N‖ := h_cs
    _ ≤ (‖mpvState (d := d) X N‖ ^ 2 + ‖mpvState (d := d) Y N‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖mpvState (d := d) X N‖ - ‖mpvState (d := d) Y N‖)]
    _ = (‖mpvInner (d := d) X X N‖ + ‖mpvInner (d := d) Y Y N‖) / 2 := by
          rw [hXX_sq N, hYY_sq N]
    _ ≤ (C_X + C_Y) / 2 := by linarith [hXX_bdd N, hYY_bdd N]

end MPSTensor
