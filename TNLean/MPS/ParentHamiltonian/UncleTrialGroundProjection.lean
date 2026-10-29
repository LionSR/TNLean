/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.UncleTrialOverlap
import TNLean.MPS.ParentHamiltonian.UncleVariationalEigenvalue

/-!
# Vanishing projection of the actual two-wall trial onto the periodic sectors

The derived trial overlaps and the asymptotic Gram matrix of the two periodic
vectors force the actual projected squared norm to vanish. This supplies the
projection-removal step for arXiv:1210.6613, proof of Theorem thm:gapless,
lines 1302–1314. The separate canonical Gram theorem discharges the explicit
Gram-limit input; the exact uncle kernel theorem identifies this span with
the full kernel for injective perturbations and sufficiently large lengths.
-/

open scoped InnerProductSpace Topology
open Filter

namespace MPSTensor

/-- The actual source trial has vanishing squared projection onto the two
periodic ground sectors. The actual overlap limits are derived from unital
normalization and mixed damping, rather than supplied as an orthogonality
premise. Source: arXiv:1210.6613, proof of Theorem thm:gapless. -/
theorem uncleTwoWallTrialSource_span_projection_tendsto_zero
    {d a b : ℕ} (A : MPSTensor d a) (B : MPSTensor d b)
    (R : Fin d → Matrix (Fin a) (Fin b) ℂ)
    (L : Fin d → Matrix (Fin b) (Fin a) ℂ)
    (hUA : Kraus.mapLM A 1 = 1) (hUB : Kraus.mapLM B 1 = 1)
    (hGram :
      Tendsto (fun M ↦ ‖mpvState A M‖ ^ 2) atTop (nhds (1 : ℝ)) ∧
        Tendsto (fun M ↦ ‖mpvState B M‖ ^ 2) atTop (nhds (1 : ℝ)) ∧
        Tendsto (fun M ↦ inner ℂ (mpvState A M) (mpvState B M)) atTop (nhds (0 : ℂ)))
    (hAB : Kraus.mixedMapSpectralRadius A B < 1)
    (hBA : Kraus.mixedMapSpectralRadius B A < 1) :
    Tendsto (fun N : ℕ ↦
      ‖(Submodule.span ℂ ({mpvState A (6 * N + 1), mpvState B (6 * N + 1)} :
          Set (EuclideanSpace ℂ (Cfg d (6 * N + 1))))).starProjection
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d (6 * N + 1))).symm
          (uncleTwoWallTrialSource A B R L N))‖ ^ 2) atTop (nhds (0 : ℝ)) := by
  have hlen : Tendsto (fun N : ℕ ↦ 6 * N + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    exact eventually_atTop.mpr ⟨M, fun N hN ↦ by omega⟩
  have hA := (hGram.1.comp hlen).eventually
    (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hB := (hGram.2.1.comp hlen).eventually
    (eventually_gt_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  have hcrossNorm : Tendsto (fun N : ℕ ↦
      ‖inner ℂ (mpvState A (6 * N + 1)) (mpvState B (6 * N + 1))‖)
      atTop (nhds (0 : ℝ)) := by
    simpa only [norm_zero] using (hGram.2.2.comp hlen).norm
  have hcross := hcrossNorm.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hleft := inner_mpvState_left_uncleTwoWallTrialSource_tendsto_zero A B R L hUA hBA
  have hright := inner_mpvState_right_uncleTwoWallTrialSource_tendsto_zero A B R L hUB hAB
  have hbound := ((hleft.norm.pow 2).add (hright.norm.pow 2)).const_mul 4
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ sq_nonneg _)
  · filter_upwards [hA, hB, hcross] with N hAN hBN hcrossN
    exact norm_mpv_span_projection_sq_le A B (6 * N + 1) _ hAN.le hBN.le hcrossN.le
  · simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero] using hbound

end MPSTensor
