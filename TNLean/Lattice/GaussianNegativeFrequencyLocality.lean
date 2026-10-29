/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianNegativeFrequencyOperator
import TNLean.Lattice.GaussianFilteredLocality

/-!
# Uniform locality of the actual regularized frequency commutator

The inverse-time Cauchy factor is cancelled at short times by the actual
Lieb–Robinson increment. At long times it is bounded by the reciprocal
cutoff time. Splitting the Gaussian probability integral gives a bound
independent of the positive Cauchy regularizer. Thus it can be used in the
actual zero-regularizer passage; no inverse-regularizer estimate substitutes
for that argument.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3, the Gaussian
frequency-separation proof following Lemma 3.1. The finite-ring caller
supplies the short-time commutator increment from actual local dynamics.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix GaussianFilter
open scoped Matrix.Norms.L2Operator NNReal

namespace TNLean.Lattice

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem norm_inv_cauchyDenominator_le_abs_time (ε : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖((ε : ℂ) - Complex.I * t)⁻¹‖ ≤ |t|⁻¹ := by
  have hnorm : |t| ≤ ‖(ε : ℂ) - Complex.I * t‖ := by
    simpa using Complex.abs_im_le_norm ((ε : ℂ) - Complex.I * t)
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (abs_pos.mpr ht) hnorm

private theorem exp_sub_one_le_mul_exp (x : ℝ) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

/-- The actual regularized frequency commutator is uniformly local in the
regularizer, once the actual Heisenberg commutator has the indicated
Lieb–Robinson increment. Its short-time zero cancels the Cauchy pole;
the long-time part is controlled by the actual Gaussian tail. This is
an intermediate form of Hastings–Koma, arXiv:math-ph/0507008,
Section 3; no ordinary correlation estimate is assumed. -/
theorem norm_commutator_gaussianNegativeFrequencyOperator_le
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A B : Matrix n n ℂ)
    {ε T C v : ℝ} (hε : 0 < ε) (hT : 0 < T) (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hLR : ∀ t : ℝ,
      ‖hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t) * B -
          B * (hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t))‖ ≤
        C * (Real.exp (v * |t|) - 1)) :
    ‖gaussianNegativeFrequencyOperator h ε H A * B -
        B * gaussianNegativeFrequencyOperator h ε H A‖ ≤
      kernel h⁻¹ 0 * (C * v * Real.exp (v * T) +
        (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (h : ℝ)))) := by
  let μ : Measure ℝ := gaussianReal 0 h
  let f := gaussianNegativeFrequencyIntegrand H A ε
  let L := commutatorCLM B
  let a : ℝ → Matrix n n ℂ := fun t ↦
    hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t)
  let M := C * v * Real.exp (v * T)
  let D := 2 * ‖A‖ * ‖B‖
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hC hv) (Real.exp_pos _).le
  have hnorm (t : ℝ) : ‖L (f t)‖ =
      ‖((ε : ℂ) - Complex.I * t)⁻¹‖ * ‖a t * B - B * a t‖ := by
    simp only [L, f, gaussianNegativeFrequencyIntegrand, map_smul, norm_smul,
      commutatorCLM_apply, a]
  have hglob (t : ℝ) : ‖a t * B - B * a t‖ ≤ D := by
    calc
      _ ≤ ‖a t * B‖ + ‖B * a t‖ := norm_sub_le _ _
      _ ≤ ‖a t‖ * ‖B‖ + ‖B‖ * ‖a t‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = D := by
        rw [SpectralFilter.norm_hermitianUnitaryPath_conj hH A t]
        dsimp only [D]
        ring
  have hshort (t : ℝ) (ht : t ∈ Set.Icc (-T) T) : ‖L (f t)‖ ≤ M := by
    rw [hnorm]
    by_cases ht0 : t = 0
    · subst t
      have hz : ‖a 0 * B - B * a 0‖ = 0 := le_antisymm
        (by simpa only [abs_zero, mul_zero, Real.exp_zero, sub_self, mul_zero] using hLR 0)
        (norm_nonneg _)
      rw [hz, mul_zero]
      exact hM
    have hs : 0 < |t| := abs_pos.mpr ht0
    have hsT : |t| ≤ T := abs_le.mpr ht
    have hcomm : ‖a t * B - B * a t‖ ≤ |t| * M := by
      calc
        _ ≤ C * (Real.exp (v * |t|) - 1) := hLR t
        _ ≤ C * ((v * |t|) * Real.exp (v * |t|)) :=
          mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp _) hC
        _ ≤ C * ((v * |t|) * Real.exp (v * T)) := by
          gcongr
        _ = _ := by dsimp only [M]; ring
    calc
      _ ≤ |t|⁻¹ * (|t| * M) :=
        mul_le_mul (norm_inv_cauchyDenominator_le_abs_time ε ht0) hcomm
          (norm_nonneg _) (inv_nonneg.mpr hs.le)
      _ = M := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have hlong (t : ℝ) (ht : t ∈ (Set.Icc (-T) T)ᶜ) : ‖L (f t)‖ ≤ D / T := by
    have hs : T < |t| := by
      by_contra hs
      exact ht (abs_le.mp (le_of_not_gt hs))
    have ht0 : t ≠ 0 := abs_pos.mp (hT.trans hs)
    have hi : ‖((ε : ℂ) - Complex.I * t)⁻¹‖ ≤ T⁻¹ :=
      (norm_inv_cauchyDenominator_le_abs_time ε ht0).trans (by
        simpa only [one_div] using one_div_le_one_div_of_le hT hs.le)
    rw [hnorm]
    calc
      _ ≤ T⁻¹ * D := mul_le_mul hi (hglob t) (norm_nonneg _) (inv_nonneg.mpr hT.le)
      _ = D / T := by rw [div_eq_mul_inv, mul_comm]
  have hint := integrable_gaussianNegativeFrequencyIntegrand h hH A hε
  have hmap : Integrable (fun t ↦ L (f t)) μ := L.integrable_comp hint
  have hmass : ‖∫ t, L (f t) ∂μ‖ ≤ M + (D / T) * μ.real (Set.Icc (-T) T)ᶜ := by
    calc
      _ ≤ ‖∫ t in Set.Icc (-T) T, L (f t) ∂μ‖ +
          ‖∫ t in (Set.Icc (-T) T)ᶜ, L (f t) ∂μ‖ := by
        rw [← integral_add_compl measurableSet_Icc hmap]
        exact norm_add_le _ _
      _ ≤ M * μ.real (Set.Icc (-T) T) + (D / T) * μ.real (Set.Icc (-T) T)ᶜ :=
        add_le_add (norm_setIntegral_le_of_norm_le_const (by finiteness) hshort)
          (norm_setIntegral_le_of_norm_le_const (by finiteness) hlong)
      _ ≤ _ := add_le_add_right (mul_le_of_le_one_right hM measureReal_le_one) _
  change ‖L (gaussianNegativeFrequencyOperator h ε H A)‖ ≤ _
  rw [gaussianNegativeFrequencyOperator, map_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (kernel_nonneg _ _), ← L.integral_comp_comm hint]
  apply mul_le_mul_of_nonneg_left ?_ (kernel_nonneg _ _)
  apply hmass.trans
  dsimp only [M, D, μ]
  gcongr
  exact gaussianReal_real_compl_Icc_le_exp h hT.le

end TNLean.Lattice
