/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianCauchyKernel
import TNLean.Lattice.GaussianCauchyNormalization
import TNLean.Lattice.GaussianNegativeFrequencyCutoff
import QICLean.Analysis.GaussianFilter.Kernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral

/-!
# The actual Gaussian--Cauchy integral as a damped half-line Gaussian

The Cauchy denominator has a Laplace representation. Its product with an
actual Gaussian characteristic phase is jointly absolutely integrable for
every positive regularizer. Fubini and the Gaussian characteristic function
therefore give the actual half-line Gaussian integral, without an assumed
Fourier-transform or interchange premise.

Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1,
equations (3.7)–(3.13). The zero-regularizer limit follows by Gaussian
domination. The actual density normalization identifies it with the
Gaussian probability cutoff.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace TNLean.Lattice

/-- The actual Gaussian-averaged Cauchy transform, at time variance \(h\),
regularizer \(\varepsilon\), and frequency \(\omega\).
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1. -/
def gaussianCauchyTransform (h : ℝ≥0) (ε ω : ℝ) : ℂ :=
  ∫ t : ℝ, ((ε : ℂ) - Complex.I * t)⁻¹ *
    Complex.exp ((ω : ℂ) * t * Complex.I) ∂gaussianReal 0 h

/-- The actual Gaussian/Cauchy integral equals its damped half-line
Gaussian transform. Joint absolute integrability is proved from the
positive regularizer; the Gaussian transform is the existing exact
characteristic function. No exchange-of-integrals hypothesis is supplied.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1,
equations (3.8)–(3.13), written with the normalized Gaussian time measure. -/
theorem gaussianCauchyTransform_eq_integral (h : ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) (ω : ℝ) :
    gaussianCauchyTransform h ε ω =
      ∫ s : ℝ in Set.Ioi 0, Complex.exp (-(ε : ℂ) * s) *
        Complex.exp (-(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2) := by
  let μ : Measure ℝ := gaussianReal 0 h
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ → ℝ → ℂ := fun t s ↦
    Complex.exp (-(ε : ℂ) * s) * Complex.exp (((ω + s : ℝ) : ℂ) * t * Complex.I)
  have hFNorm (t s : ℝ) : ‖F t s‖ = Real.exp (-ε * s) := by
    simp [F, Complex.norm_exp]
  have hdecay : Integrable (fun s : ℝ ↦ Real.exp (-ε * s)) ν :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0
  have hmajor : Integrable (fun p : ℝ × ℝ ↦ (1 : ℝ) * Real.exp (-ε * p.2))
      (μ.prod ν) :=
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ ↦ (1 : ℝ)) μ).mul_prod hdecay
  have hJoint : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply hmajor.mono'
    · apply Continuous.aestronglyMeasurable
      dsimp only [Function.uncurry, F]
      fun_prop
    · exact Filter.Eventually.of_forall fun p ↦ by
        change ‖F p.1 p.2‖ ≤ 1 * Real.exp (-ε * p.2)
        rw [hFNorm, one_mul]
  have hLaplace (t : ℝ) :
      ((ε : ℂ) - Complex.I * t)⁻¹ * Complex.exp ((ω : ℂ) * t * Complex.I) =
        ∫ s, F t s ∂ν := by
    rw [inv_cauchyDenominator_eq_integral hε t, ← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s ↦ by
      dsimp only [F]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
  calc
    gaussianCauchyTransform h ε ω = ∫ t, ∫ s, F t s ∂ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hLaplace
    _ = ∫ s, ∫ t, F t s ∂μ ∂ν := integral_integral_swap hJoint
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s ↦ by
        dsimp only [F]
        rw [integral_const_mul, GaussianFilter.integral_cexp h (ω + s)]

/-- The actual Gaussian/Cauchy transform has the source half-line Gaussian
limit as the positive regularizer tends to zero. Dominated convergence is
proved with the translated Gaussian as an integrable majorant; the divergent
crude inverse-regularizer bound is not used for this passage.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1, equation (3.7),
before converting the Gaussian integral to its normalized tail. -/
theorem tendsto_gaussianCauchyTransform_zero_regularizer
    (h : ℝ≥0) (hh : 0 < h) (ω : ℝ) :
    Filter.Tendsto (fun ε : ℝ ↦ gaussianCauchyTransform h ε ω) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s : ℝ in Set.Ioi 0,
        Complex.exp (-(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2))) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let g : ℝ → ℝ := fun s ↦ Real.exp (-(h : ℝ) * (ω + s) ^ 2 / 2)
  let G : ℝ → ℂ := fun s ↦ Complex.exp (-(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2)
  let F : ℝ → ℝ → ℂ := fun ε s ↦ Complex.exp (-(ε : ℂ) * s) * G s
  have hhReal : 0 < (h : ℝ) := by exact_mod_cast hh
  have hGNorm (s : ℝ) : ‖G s‖ = g s := by
    have hcast : -(h : ℂ) * ((ω + s : ℝ) : ℂ) ^ 2 / 2 =
        ((-(h : ℝ) * (ω + s) ^ 2 / 2 : ℝ) : ℂ) := by push_cast <;> ring
    dsimp only [G, g]
    rw [hcast, ← Complex.ofReal_exp, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hg : Integrable g ν := by
    have hbase := (integrable_exp_neg_mul_sq (half_pos hhReal)).comp_add_left ω
    have hfull : Integrable g := hbase.congr (Filter.Eventually.of_forall fun s ↦ by
      dsimp only [g]
      congr 1
      ring)
    exact hfull.integrableOn
  have hmeas : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), AEStronglyMeasurable (F ε) ν :=
    Filter.Eventually.of_forall fun ε ↦ by
      apply Continuous.aestronglyMeasurable
      dsimp only [F, G]
      fun_prop
  have hbound : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ s ∂ν, ‖F ε s‖ ≤ g s := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hεpos : 0 < ε := hε
    have hspos : 0 < s := hs
    have hdecay : Real.exp (-ε * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hfirst : ‖Complex.exp (-(ε : ℂ) * s)‖ = Real.exp (-ε * s) := by
      simp [Complex.norm_exp]
    dsimp only [F]
    rw [norm_mul, hfirst, hGNorm]
    calc
      _ ≤ 1 * g s := mul_le_mul_of_nonneg_right hdecay (Real.exp_pos _).le
      _ = _ := one_mul _
  have hlim : ∀ᵐ s ∂ν, Filter.Tendsto (fun ε : ℝ ↦ F ε s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (G s)) :=
    Filter.Eventually.of_forall fun s ↦ by
      have hcont : Continuous fun ε : ℝ ↦ F ε s := by dsimp only [F]; fun_prop
      simpa only [F, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul] using
        (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hint := tendsto_integral_filter_of_dominated_convergence g hmeas hbound hg hlim
  apply hint.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (gaussianCauchyTransform_eq_integral h hε ω).symm

/-- The actual normalized Gaussian/Cauchy transform converges to the
Gaussian probability tail. Its normalization is the density at zero of
the inverse-variance Gaussian, with no supplied transform identity.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1, equation (3.7). -/
theorem tendsto_normalized_gaussianCauchyTransform
    (h : ℝ≥0) (hh : 0 < h) (ω : ℝ) :
    Filter.Tendsto (fun ε : ℝ ↦ (GaussianFilter.kernel h⁻¹ 0 : ℂ) *
      gaussianCauchyTransform h ε ω) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((gaussianReal 0 h⁻¹).real (Set.Ici ω) : ℂ)) := by
  have hlim := (tendsto_gaussianCauchyTransform_zero_regularizer h hh ω).const_mul
    (GaussianFilter.kernel h⁻¹ 0 : ℂ)
  simpa only [GaussianFilter.halfLine_gaussian_integral_eq_measureReal h hh ω] using hlim

/-- The actual source Gaussian parameters give the frequency cutoff whose
positive- and negative-gap errors are bounded by \(e^{-q/2}\). This proves
the scalar Cauchy/Gaussian limit identity rather than assuming a Fourier
or approximation premise. Source: Hastings–Koma, arXiv:math-ph/0507008,
Lemma 3.1, equation (3.7), with \(\alpha=\Delta^2/(2q)\). -/
theorem tendsto_normalized_gaussianCauchyTransform_cutoff
    {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) (ω : ℝ) :
    let h := (q / Δ ^ 2).toNNReal
    Filter.Tendsto (fun ε : ℝ ↦ (GaussianFilter.kernel h⁻¹ 0 : ℂ) *
      gaussianCauchyTransform h ε ω) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (gaussianNegativeFrequencyCutoff q Δ ω : ℂ)) := by
  let h := (q / Δ ^ 2).toNNReal
  have hh : 0 < h := Real.toNNReal_pos.mpr (by positivity)
  have hinv : h⁻¹ = (Δ ^ 2 / q).toNNReal := by
    apply NNReal.coe_injective
    dsimp only [h]
    rw [NNReal.coe_inv, Real.coe_toNNReal _ (div_nonneg hq.le (sq_nonneg Δ)),
      Real.coe_toNNReal _ (div_nonneg (sq_nonneg Δ) hq.le), inv_div]
  have hcut : gaussianNegativeFrequencyCutoff q Δ ω =
      (gaussianReal 0 h⁻¹).real (Set.Ici ω) := by
    rw [gaussianNegativeFrequencyCutoff, hinv]
  change Filter.Tendsto (fun ε : ℝ ↦ (GaussianFilter.kernel h⁻¹ 0 : ℂ) *
    gaussianCauchyTransform h ε ω) (nhdsWithin 0 (Set.Ioi 0))
    (nhds (gaussianNegativeFrequencyCutoff q Δ ω : ℂ))
  rw [hcut]
  exact tendsto_normalized_gaussianCauchyTransform h hh ω

end TNLean.Lattice
