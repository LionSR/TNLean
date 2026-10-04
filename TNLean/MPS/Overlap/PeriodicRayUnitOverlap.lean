/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Symmetry.PeriodicMPSNormLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Unit asymptotic overlap from periodic lines and transfer contraction

Equality of the one-dimensional periodic spans makes the overlap modulus the
product of the state norms. A strict bound on all nonunit transfer eigenvalues
makes those norms converge to one for a unital tensor with simple fixed space.
Together these observations give unit asymptotic overlap without choosing
continuous proportionality scalars.

Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. The transfer
spectral bound is supplied; no bound is deduced from a physical Hamiltonian gap.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open scoped Matrix Topology
open Filter

namespace MPSTensor

/-- Equal periodic spans give equality in the overlap norm bound, including
when both vectors vanish. Source context: arXiv:1010.3732, Appendix C,
lines 2653–2717, comparison of the limiting periodic lines. -/
theorem norm_mpvOverlap_eq_mul_norm_of_span_eq
    {d D E N : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (hspan : Submodule.span ℂ {(mpv A : (Fin N → Fin d) → ℂ)} =
      Submodule.span ℂ {(mpv B : (Fin N → Fin d) → ℂ)}) :
    ‖mpvOverlap A B N‖ = ‖mpvState A N‖ * ‖mpvState B N‖ := by
  have hmem : (mpv B : (Fin N → Fin d) → ℂ) ∈
      Submodule.span ℂ {(mpv A : (Fin N → Fin d) → ℂ)} := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hstate : mpvState B N = c • mpvState A N := by
    apply PiLp.ext
    intro x
    simpa only [mpvState_apply, PiLp.smul_apply, Pi.smul_apply] using congrFun hc.symm x
  rw [mpvOverlap_eq_star_mpvInner, norm_star, mpvInner, hstate,
    inner_smul_right, norm_mul, ← inner_self_re_eq_norm, inner_self_eq_norm_sq, norm_smul]
  ring

/-- A unital tensor with one-dimensional transfer fixed space and strictly
contracting remaining transfer spectrum has periodic state norm tending to
one. Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. The transfer
spectral bound is an explicit auxiliary hypothesis. -/
theorem norm_mpvState_tendsto_one_of_transfer_spectrum
    {d D : ℕ} [NeZero D] (A : MPSTensor d D) (hUnital : Kraus.IsUnital A)
    (hDim : Module.finrank ℂ (Module.End.eigenspace (Kraus.transferMap A) 1) = 1)
    (q : ℝ) (hq : 0 ≤ q) (hqOne : q < 1)
    (hspec : ∀ z ∈ spectrum ℂ (Kraus.transferMap A), z ≠ 1 → ‖z‖ ≤ q) :
    Tendsto (fun N => ‖mpvState A N‖) atTop (𝓝 (1 : ℝ)) := by
  have hDiff : Tendsto (fun N => ‖mpvState A N‖ ^ 2 - 1) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm' (a := fun N => (D * D - 1 : ℕ) * q ^ N)
    · exact Filter.Eventually.of_forall fun N => by
        simpa only [Real.norm_eq_abs] using
          abs_norm_mpvState_sq_sub_one_le_of_transfer_spectrum A hUnital hDim q hspec N
    · simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq hqOne).const_mul ((D * D - 1 : ℕ) : ℝ)
  have hSq : Tendsto (fun N => ‖mpvState A N‖ ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [sub_add_cancel, zero_add] using hDiff.add_const 1
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_one] using
    (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hSq

/-- Eventual equality of periodic spans and convergence of both state norms
to one imply a unit limiting overlap modulus. No proportionality scalars
are chosen. Source context: arXiv:1010.3732, Appendix C, lines 2653–2717. -/
theorem norm_mpvOverlap_tendsto_one_of_eventual_span_eq
    {d D E : ℕ} (A : MPSTensor d D) (B : MPSTensor d E)
    (hspan : ∀ᶠ N in atTop,
      Submodule.span ℂ {(mpv A : (Fin N → Fin d) → ℂ)} =
        Submodule.span ℂ {(mpv B : (Fin N → Fin d) → ℂ)})
    (hA : Tendsto (fun N => ‖mpvState A N‖) atTop (𝓝 (1 : ℝ)))
    (hB : Tendsto (fun N => ‖mpvState B N‖) atTop (𝓝 (1 : ℝ))) :
    Tendsto (fun N => ‖mpvOverlap A B N‖) atTop (𝓝 (1 : ℝ)) := by
  have hEq : (fun N => ‖mpvOverlap A B N‖) =ᶠ[atTop]
      (fun N => ‖mpvState A N‖ * ‖mpvState B N‖) := by
    filter_upwards [hspan] with N hN
    exact norm_mpvOverlap_eq_mul_norm_of_span_eq A B hN
  exact (tendsto_congr' hEq).mpr (by simpa only [one_mul] using hA.mul hB)

end MPSTensor
