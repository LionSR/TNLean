/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.Basic
import Mathlib.Analysis.Normed.Group.Continuity


/-!
# Asymptotic overlaps under periodic decompositions

If a periodic vector is the sum of a retained component and a remainder whose
norm tends to zero, the remainder contributes vanishing overlap against any
eventually bounded periodic family. In particular, removing it preserves an
overlap modulus tending to one. The decomposition is needed only eventually
in the chain length, so no identity at length zero is required.

These are auxiliary asymptotic results in the context of arXiv:1010.3732,
Appendix C, lines 2653–2717. No equality of the retained and original periodic
rays, or implication from a physical spectral gap, is asserted.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Topology InnerProductSpace
open Filter

namespace MPSTensor

private theorem norm_mpvOverlap_sub_le_of_decomposition
    {d D E F K : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (C : MPSTensor d F) (R : MPSTensor d K) (N : ℕ)
    (hdecomp : ∀ σ : Fin N → Fin d, mpv B σ = mpv C σ + mpv R σ) :
    ‖mpvOverlap A B N - mpvOverlap A C N‖ ≤
      ‖mpvState A N‖ * ‖mpvState R N‖ := by
  rw [mpvOverlap_eq_star_mpvInner, mpvOverlap_eq_star_mpvInner]
  have hstate : mpvState B N = mpvState C N + mpvState R N := by
    apply PiLp.ext
    exact fun σ => by simpa only [PiLp.add_apply, mpvState_apply] using hdecomp σ
  simp only [mpvInner, hstate, inner_add_right, star_add, add_sub_cancel_left, norm_star]
  exact norm_inner_le_norm _ _

/-- A periodic remainder whose norm tends to zero does not contribute to the
limiting overlap with an eventually bounded periodic state. This is an
auxiliary asymptotic statement for arXiv:1010.3732, Appendix C, lines 2653–2717;
no exact equality of the supported periodic rays is assumed. -/
theorem mpvOverlap_sub_tendsto_zero_of_eventual_decomposition
    {d D E F K : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (C : MPSTensor d F) (R : MPSTensor d K) (M : ℝ)
    (hA : ∀ᶠ N in atTop, ‖mpvState A N‖ ≤ M)
    (hdecomp : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv B σ = mpv C σ + mpv R σ)
    (hR : Tendsto (fun N => ‖mpvState R N‖) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun N => mpvOverlap A B N - mpvOverlap A C N)
      atTop (𝓝 (0 : ℂ)) := by
  apply squeeze_zero_norm' (a := fun N => M * ‖mpvState R N‖)
  · filter_upwards [hA, hdecomp] with N hAN hN
    exact (norm_mpvOverlap_sub_le_of_decomposition A B C R N hN).trans
      (mul_le_mul_of_nonneg_right hAN (norm_nonneg _))
  · simpa only [mul_zero] using hR.const_mul M

/-- Removing a norm-vanishing periodic remainder preserves an overlap modulus
that tends to one. This is an auxiliary asymptotic statement for
arXiv:1010.3732, Appendix C, lines 2653–2717. It asserts asymptotic overlap
preservation after compression. -/
theorem mpvOverlap_norm_tendsto_one_of_eventual_decomposition
    {d D E F K : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (C : MPSTensor d F) (R : MPSTensor d K) (M : ℝ)
    (hA : ∀ᶠ N in atTop, ‖mpvState A N‖ ≤ M)
    (hdecomp : ∀ᶠ N in atTop, ∀ σ : Fin N → Fin d,
      mpv B σ = mpv C σ + mpv R σ)
    (hR : Tendsto (fun N => ‖mpvState R N‖) atTop (𝓝 (0 : ℝ)))
    (hOverlap : Tendsto (fun N => ‖mpvOverlap A B N‖) atTop (𝓝 (1 : ℝ))) :
    Tendsto (fun N => ‖mpvOverlap A C N‖) atTop (𝓝 (1 : ℝ)) := by
  apply hOverlap.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun N => dist_norm_norm_le (mpvOverlap A B N) (mpvOverlap A C N))
  simpa only [norm_zero] using
    (mpvOverlap_sub_tendsto_zero_of_eventual_decomposition A B C R M hA hdecomp hR).norm

end MPSTensor
