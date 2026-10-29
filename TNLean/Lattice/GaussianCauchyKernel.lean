/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The actual regularized Cauchy kernel for frequency separation

For positive Gaussian width and positive Cauchy regularizer, the source
Gaussian/Cauchy Fourier integral is absolutely integrable. The denominator
has an actual half-line Laplace representation. These are prerequisites
for interchanging its two integrals and taking the regularizer to zero.

Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1,
equations (3.7)–(3.14). No Fourier/Cauchy limit identity is assumed.
-/

noncomputable section

open MeasureTheory

namespace TNLean.Lattice

/-- The regularized negative-frequency time kernel. The rational factor
is \(i/(t+i\varepsilon)=1/(\varepsilon-it)\).
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.8). -/
def gaussianCauchyKernel (α ε t : ℝ) : ℂ :=
  (Real.exp (-α * t ^ 2) / (2 * Real.pi) : ℝ) *
    ((ε : ℂ) - Complex.I * t)⁻¹

/-- The regularized Cauchy denominator is nonzero at every real time.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.8). -/
theorem cauchyDenominator_ne_zero {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (ε : ℂ) - Complex.I * t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have : ε = 0 := by simpa using hre
  exact hε.ne' this

/-- The rational Cauchy factor is bounded by the reciprocal of its
positive regularizer. Source: Hastings–Koma, arXiv:math-ph/0507008,
equation (3.8). -/
theorem norm_inv_cauchyDenominator_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖((ε : ℂ) - Complex.I * t)⁻¹‖ ≤ ε⁻¹ := by
  have hnorm : ε ≤ ‖(ε : ℂ) - Complex.I * t‖ := by
    simpa using Complex.re_le_norm ((ε : ℂ) - Complex.I * t)
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hε hnorm

/-- The rational source kernel has a convergent half-line Laplace
representation whenever the regularizer is positive. This is the scalar
identity needed before the Gaussian Fourier interchange.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1. -/
theorem inv_cauchyDenominator_eq_integral {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ((ε : ℂ) - Complex.I * t)⁻¹ =
      ∫ s : ℝ in Set.Ioi 0, Complex.exp ((-(ε : ℂ) + Complex.I * t) * s) := by
  have ha : (-(ε : ℂ) + Complex.I * t).re < 0 := by simpa using neg_lt_zero.mpr hε
  rw [integral_exp_mul_complex_Ioi ha 0]
  have hsign : -(ε : ℂ) + Complex.I * t = -((ε : ℂ) - Complex.I * t) := by ring
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [hsign, neg_div_neg_eq, one_div]

/-- The actual Gaussian/Cauchy kernel is bounded by an integrable Gaussian
when its regularizer is positive. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equation (3.8). -/
theorem norm_gaussianCauchyKernel_le {ε : ℝ} (hε : 0 < ε) (α t : ℝ) :
    ‖gaussianCauchyKernel α ε t‖ ≤
      (2 * Real.pi * ε)⁻¹ * Real.exp (-α * t ^ 2) := by
  rw [gaussianCauchyKernel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (Real.exp (-α * t ^ 2) / (2 * Real.pi)) * ε⁻¹ :=
      mul_le_mul_of_nonneg_left (norm_inv_cauchyDenominator_le hε t) (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero, hε.ne']

/-- Multiplying the regularized kernel by the actual frequency phase
preserves absolute integrability. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equation (3.8). -/
theorem integrable_gaussianCauchyKernel_mul_exp {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (ω : ℝ) :
    Integrable (fun t : ℝ ↦ gaussianCauchyKernel α ε t *
      Complex.exp (Complex.I * ω * t)) := by
  have hcont : Continuous fun t : ℝ ↦ gaussianCauchyKernel α ε t *
      Complex.exp (Complex.I * ω * t) := by
    unfold gaussianCauchyKernel
    apply Continuous.mul
    · apply Continuous.mul
      · exact Complex.continuous_ofReal.comp (by fun_prop)
      · exact (by fun_prop : Continuous fun t : ℝ ↦ (ε : ℂ) - Complex.I * t).inv₀
          (cauchyDenominator_ne_zero hε)
    · fun_prop
  apply ((integrable_exp_neg_mul_sq hα).const_mul (2 * Real.pi * ε)⁻¹).mono'
    hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hphase : ‖Complex.exp (Complex.I * ω * t)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [norm_mul, hphase, mul_one]
  exact norm_gaussianCauchyKernel_le hε α t

/-- A finite explicit bound for the actual regularized frequency integral.
Its dependence on the regularizer is retained; this is not a uniform
regularizer-limit or locality bound. Source: Hastings–Koma,
arXiv:math-ph/0507008, equation (3.8). -/
theorem norm_integral_gaussianCauchyKernel_mul_exp_le {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) (ω : ℝ) :
    ‖∫ t : ℝ, gaussianCauchyKernel α ε t * Complex.exp (Complex.I * ω * t)‖ ≤
      (2 * Real.pi * ε)⁻¹ * Real.sqrt (Real.pi / α) := by
  have hnorm (t : ℝ) :
      ‖gaussianCauchyKernel α ε t * Complex.exp (Complex.I * ω * t)‖ ≤
        (2 * Real.pi * ε)⁻¹ * Real.exp (-α * t ^ 2) := by
    have hphase : ‖Complex.exp (Complex.I * ω * t)‖ = 1 := by
      simp [Complex.norm_exp]
    rw [norm_mul, hphase, mul_one]
    exact norm_gaussianCauchyKernel_le hε α t
  calc
    _ ≤ ∫ t : ℝ, (2 * Real.pi * ε)⁻¹ * Real.exp (-α * t ^ 2) :=
      norm_integral_le_of_norm_le
        ((integrable_exp_neg_mul_sq hα).const_mul _) (Filter.Eventually.of_forall hnorm)
    _ = _ := by rw [integral_const_mul, integral_gaussian α]

end TNLean.Lattice
