/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Overlap.Basic

/-!
# Self-overlap convergence auxiliaries

This module collects small auxiliary lemmas about the convergence of MPV self-overlaps
used by both the BNT Permutation Rigidity argument and the Fundamental Theorem helpers.

## Main statements

* `tendsto_norm_selfOverlap_one`: normed form of a self-overlap tending to `1`.
* `tendsto_norm_mpvState_one`: MPV-state norm form of a self-overlap tending to `1`.

## Tags

matrix product states, overlap, convergence
-/

open Filter

namespace MPSTensor

variable {d : ℕ}

/-- Norm-convergence form of normalized self-overlap convergence. -/
lemma tendsto_norm_selfOverlap_one
    {D : ℕ} (A : MPSTensor d D)
    (hA : Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ))) :
    Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1) := by
  simpa [norm_one] using hA.norm

/-- MPV-state norm-convergence form of normalized self-overlap convergence.

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. In the
block-selection contradiction, normalized BNT blocks have self-overlap tending
to one; this lemma rewrites that normalization as convergence of the Hilbert
space norm of the corresponding MPV state. -/
lemma tendsto_norm_mpvState_one
    {D : ℕ} (A : MPSTensor d D)
    (hA : Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ))) :
    Tendsto (fun N => ‖mpvState (d := d) A N‖) atTop (nhds (1 : ℝ)) := by
  have hInner : Tendsto (fun N => mpvInner (d := d) A A N) atTop (nhds (1 : ℂ)) := by
    simpa [mpvOverlap_eq_star_mpvInner] using hA.star
  have hNormInner :
      Tendsto (fun N => ‖mpvInner (d := d) A A N‖) atTop (nhds (1 : ℝ)) := by
    simpa [norm_one] using hInner.norm
  have hSq :
      (fun N => ‖mpvState (d := d) A N‖ ^ 2) =
        fun N => ‖mpvInner (d := d) A A N‖ := by
    funext N
    have heq :
        mpvInner (d := d) A A N =
          ↑(‖mpvState (d := d) A N‖ ^ 2 : ℝ) := by
      unfold mpvInner
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [heq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hSq_tendsto :
      Tendsto (fun N => ‖mpvState (d := d) A N‖ ^ 2) atTop (nhds (1 : ℝ)) :=
    hNormInner.congr' (Filter.Eventually.of_forall fun N => (hSq ▸ rfl : _))
  have hSqrt :
      Tendsto (fun N => Real.sqrt (‖mpvState (d := d) A N‖ ^ 2))
        atTop (nhds (Real.sqrt (1 : ℝ))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hSq_tendsto
  simpa [Real.sqrt_sq, norm_nonneg] using hSqrt

end MPSTensor
