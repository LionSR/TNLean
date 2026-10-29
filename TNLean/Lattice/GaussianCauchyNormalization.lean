/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.GaussianFilter.Kernel
import Mathlib.MeasureTheory.Group.Integral

/-!
# Normalization of the half-line frequency Gaussian

The half-line Gaussian with precision h becomes the actual centered Gaussian
probability tail of variance h⁻¹ after multiplication by its density at zero.
The identity follows from the existing density formula and translation
invariance of Lebesgue integration. The open and closed endpoints agree
because Lebesgue measure has no atoms.

Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1,
equations (3.7)–(3.13), with precision h and frequency threshold ω.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace GaussianFilter

/-- Normalize the actual half-line frequency integral to the centered
Gaussian tail of inverse variance. No density, integral or normalization
identity is supplied as a premise. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equations (3.7)–(3.13). -/
theorem halfLine_gaussian_integral_eq_measureReal
    (h : ℝ≥0) (hh : 0 < h) (ω : ℝ) :
    (kernel h⁻¹ 0 : ℂ) *
        (∫ s : ℝ in Set.Ioi 0,
          Complex.exp (-(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2)) =
      ((gaussianReal 0 h⁻¹).real (Set.Ici ω) : ℂ) := by
  have hhReal : 0 < (h : ℝ) := by exact_mod_cast hh
  have hdensity (t : ℝ) :
      (kernel h⁻¹ t : ℂ) = (kernel h⁻¹ 0 : ℂ) *
        Complex.exp (-(h : ℂ) * (t : ℂ) ^ 2 / 2) := by
    have hexponent : -t ^ 2 / (2 * ((h⁻¹ : ℝ≥0) : ℝ)) =
        -(h : ℝ) * t ^ 2 / 2 := by
      rw [NNReal.coe_inv]
      field_simp [hhReal.ne'] <;> ring
    have hreal : kernel h⁻¹ t = kernel h⁻¹ 0 *
        Real.exp (-(h : ℝ) * t ^ 2 / 2) := by
      simp only [kernel_eq, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div,
        Real.exp_zero, mul_one, hexponent]
    have hcast : -(h : ℂ) * (t : ℂ) ^ 2 / 2 =
        ((-(h : ℝ) * t ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hreal, Complex.ofReal_mul, hcast, Complex.ofReal_exp]
  have htranslate :
      (∫ s : ℝ in Set.Ioi 0, (kernel h⁻¹ (ω + s) : ℂ)) =
        ∫ t : ℝ in Set.Ioi ω, (kernel h⁻¹ t : ℂ) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    calc
      _ = ∫ s : ℝ, (Set.Ioi ω).indicator (fun t ↦ (kernel h⁻¹ t : ℂ)) (ω + s) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s ↦ by
          simp only [Set.indicator, Set.mem_Ioi, lt_add_iff_pos_right]
      _ = _ := integral_add_left_eq_self
        ((Set.Ioi ω).indicator (fun t ↦ (kernel h⁻¹ t : ℂ))) ω
  calc
    _ = ∫ s : ℝ in Set.Ioi 0, (kernel h⁻¹ (ω + s) : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s ↦ (hdensity (ω + s)).symm
    _ = ∫ t : ℝ in Set.Ioi ω, (kernel h⁻¹ t : ℂ) := htranslate
    _ = ((∫ t : ℝ in Set.Ici ω, kernel h⁻¹ t) : ℂ) := by
      rw [← integral_Ici_eq_integral_Ioi, integral_ofReal]
    _ = _ := congrArg Complex.ofReal
      (integral_kernel_eq_measureReal (inv_ne_zero hh.ne') (Set.Ici ω))

end GaussianFilter
