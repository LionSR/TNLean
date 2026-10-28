/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.BernsteinExponentialBound
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.Convex.Integral

/-!
# Trace-exponential bounds on general probability spaces

For an almost everywhere bounded measurable Hermitian random matrix, Lieb's
concavity gives the trace-exponential Jensen inequality. Integrability of both
matrix and scalar functions is derived from boundedness and continuity on a
compact matrix ball. Functional calculus gives a strictly positive uniform lower
bound for its exponential, so Jensen is applied on a closed convex subset of the
positive-definite cone.

For a centered bounded Hermitian random matrix, the Bernstein majorant also gives
the variance-sensitive bound on the logarithmic moment generating function. All
integrability and positivity properties used by that estimate are derived.

These are the bounded-sample analytic steps of Tropp, *User-friendly tail bounds
for sums of random matrices*, Corollary 3.3 and the proof of Theorem 6.1(ii):
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
The independent-sample iteration and general probability tail inequality remain
separate results.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open MeasureTheory

namespace Matrix

noncomputable local instance {n : Type*} [Fintype n] [DecidableEq n] :
    NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _

private theorem integral_trace_exp_add_log_le {Ω n : Type*}
    [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Ω → Matrix n n ℂ)
    {δ : ℝ} (hδ : 0 < δ)
    (hlower : ∀ᵐ ω ∂μ, δ • (1 : Matrix n n ℂ) ≤ A ω)
    (hA : Integrable A μ)
    (hF : Integrable (fun ω ↦ (NormedSpace.exp (H + CFC.log (A ω))).trace.re) μ) :
    (∫ ω, (NormedSpace.exp (H + CFC.log (A ω))).trace.re ∂μ) ≤
      (NormedSpace.exp (H + CFC.log (∫ ω, A ω ∂μ))).trace.re := by
  let s : Set (Matrix n n ℂ) := Set.Ici (δ • (1 : Matrix n n ℂ))
  have hpos {B : Matrix n n ℂ} (hB : B ∈ s) : B.PosDef := by
    have hp := ((Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef).smul hδ).add_posSemidef
      (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hB :
        0 ≤ B - δ • (1 : Matrix n n ℂ)))
    convert hp using 1
    abel
  have hc := (concaveOn_trace_exp_add_log hH).subset (fun B hB ↦ hpos hB) (convex_Ici _)
  have hcontLog : ContinuousOn CFC.log s := CFC.continuousOn_log.mono
    (fun B hB ↦ ⟨(hpos hB).isHermitian.isSelfAdjoint, (hpos hB).isUnit⟩)
  have hcont : ContinuousOn (fun B : Matrix n n ℂ ↦
      (NormedSpace.exp (H + CFC.log B)).trace.re) s := by
    have htr : Continuous (fun B : Matrix n n ℂ ↦ B.trace.re) :=
      Complex.continuous_re.comp continuous_id.matrix_trace
    exact htr.comp_continuousOn
      (NormedSpace.exp_continuous.comp_continuousOn (continuousOn_const.add hcontLog))
  exact hc.le_map_integral hcont isClosed_Ici hlower hA hF

/-- A continuous function of a measurable almost everywhere bounded finite matrix
family is integrable on a finite measure space. Compactness supplies the bound. -/
theorem integrable_continuous_comp_of_ae_norm_le
    {Ω n F : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    [NormedAddCommGroup F] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → Matrix n n ℂ} (hY : AEStronglyMeasurable Y μ) {R : ℝ}
    (hnorm : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) {g : Matrix n n ℂ → F} (hg : Continuous g) :
    Integrable (fun ω ↦ g (Y ω)) μ := by
  have hcompact := (isCompact_closedBall (0 : Matrix n n ℂ) R).image hg
  obtain ⟨C, hC⟩ := hcompact.isBounded.exists_norm_le
  apply Integrable.of_bound (hg.comp_aestronglyMeasurable hY) C
  filter_upwards [hnorm] with ω hω
  exact hC _ ⟨Y ω, by simpa only [Metric.mem_closedBall, dist_zero_right] using hω, rfl⟩

private theorem exp_neg_norm_smul_one_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {R : ℝ} (hnorm : ‖Y‖ ≤ R) :
    Real.exp (-R) • (1 : Matrix n n ℂ) ≤ NormedSpace.exp Y := by
  rw [← Algebra.algebraMap_eq_smul_one, ← CFC.real_exp_eq_normedSpace_exp hY.isSelfAdjoint]
  apply algebraMap_le_cfc Real.exp (Real.exp (-R)) Y
  intro x hx
  apply Real.exp_le_exp.mpr
  have hxnorm : |x| ≤ R := (spectrum.norm_le_norm_of_mem hx).trans hnorm
  exact (abs_le.mp hxnorm).1

/-- The trace-exponential Jensen inequality for an almost everywhere bounded
Hermitian random matrix on an arbitrary probability space. This is the bounded
specialization of Tropp, Corollary 3.3, needed in its Bernstein argument. -/
theorem integral_trace_exp_add_le_trace_exp_log_integral_exp {Ω n : Type*}
    [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {Y : Ω → Matrix n n ℂ}
    (hYmeas : AEStronglyMeasurable Y μ) (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    {R : ℝ} (hnorm : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R) :
    (∫ ω, (NormedSpace.exp (H + Y ω)).trace.re ∂μ) ≤
      (NormedSpace.exp (H + CFC.log (∫ ω, NormedSpace.exp (Y ω) ∂μ))).trace.re := by
  have hG : Continuous (fun Z : Matrix n n ℂ ↦ (NormedSpace.exp (H + Z)).trace.re) :=
    Complex.continuous_re.comp (NormedSpace.exp_continuous.comp
      (continuous_const.add continuous_id)).matrix_trace
  have hiA := integrable_continuous_comp_of_ae_norm_le hYmeas hnorm NormedSpace.exp_continuous
  have hiG := integrable_continuous_comp_of_ae_norm_le hYmeas hnorm hG
  have hident : (fun ω ↦ (NormedSpace.exp (H + CFC.log (NormedSpace.exp (Y ω)))).trace.re) =ᵐ[μ]
      (fun ω ↦ (NormedSpace.exp (H + Y ω)).trace.re) := by
    filter_upwards [hY] with ω hω
    rw [CFC.log_exp _ hω.isSelfAdjoint]
  have hlow : ∀ᵐ ω ∂μ, Real.exp (-R) • (1 : Matrix n n ℂ) ≤ NormedSpace.exp (Y ω) := by
    filter_upwards [hY, hnorm] with ω hω hωnorm
    exact exp_neg_norm_smul_one_le hω hωnorm
  have hj := integral_trace_exp_add_log_le hH (fun ω ↦ NormedSpace.exp (Y ω))
    (Real.exp_pos (-R)) hlow hiA (hiG.congr hident.symm)
  rwa [integral_congr_ae hident] at hj

/-- The variance-sensitive logarithmic moment generating function estimate for a
centered bounded Hermitian random matrix. This is the Bernstein exponential
majorant used in Tropp, the proof of Theorem 6.1(ii), on a general probability space. -/
theorem log_integral_exp_le_bernstein
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → Matrix n n ℂ}
    (hZmeas : AEStronglyMeasurable Z μ) (hZ : ∀ᵐ ω ∂μ, (Z ω).IsHermitian)
    (hmean : ∫ ω, Z ω ∂μ = 0) {R θ : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3)
    (hnorm : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ R) :
    CFC.log (∫ ω, NormedSpace.exp (θ • Z ω) ∂μ) ≤
      (θ ^ 2 / (2 * (1 - θ * R / 3)) * ‖∫ ω, Z ω ^ 2 ∂μ‖) •
        (1 : Matrix n n ℂ) := by
  let c : ℝ := θ ^ 2 / (2 * (1 - θ * R / 3))
  let M : Matrix n n ℂ := ∫ ω, NormedSpace.exp (θ • Z ω) ∂μ
  let V : Matrix n n ℂ := ∫ ω, Z ω ^ 2 ∂μ
  have hc : 0 ≤ c := by
    dsimp [c]
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hiZ : Integrable Z μ := Integrable.of_bound hZmeas R hnorm
  have hiV := integrable_continuous_comp_of_ae_norm_le hZmeas hnorm
    (continuous_id.pow 2)
  have hiM := integrable_continuous_comp_of_ae_norm_le hZmeas hnorm
    (NormedSpace.exp_continuous.comp (continuous_id.const_smul θ))
  have hVae : ∀ᵐ ω ∂μ, (0 : Matrix n n ℂ) ≤ Z ω ^ 2 := by
    filter_upwards [hZ] with ω hω
    simpa only [pow_two, hω.eq] using (posSemidef_conjTranspose_mul_self (Z ω)).nonneg
  have hVnonneg : 0 ≤ V := integral_nonneg_of_ae hVae
  have hVle : V ≤ ‖V‖ • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (IsSelfAdjoint.of_nonneg hVnonneg).le_algebraMap_norm_self
  have hle : M ≤ 1 + c • V := by
    have hiR : Integrable (fun ω ↦ 1 + θ • Z ω + c • Z ω ^ 2) μ :=
      ((integrable_const _).add (hiZ.smul θ)).add (hiV.smul c)
    have hs := integral_mono_ae (f := fun ω ↦ NormedSpace.exp (θ • Z ω))
      (g := fun ω ↦ 1 + θ • Z ω + c • Z ω ^ 2) hiM hiR (by
      filter_upwards [hZ, hnorm] with ω hω hωnorm
      exact exp_smul_le_bernstein hω hR hθ hθR hωnorm)
    change M ≤ ∫ ω, (1 : Matrix n n ℂ) + θ • Z ω + c • Z ω ^ 2 ∂μ at hs
    rw [integral_add (f := fun ω ↦ 1 + θ • Z ω) (g := fun ω ↦ c • Z ω ^ 2)
      ((integrable_const _).add (hiZ.smul θ)) (hiV.smul c),
      integral_add (f := fun _ : Ω ↦ (1 : Matrix n n ℂ)) (g := fun ω ↦ θ • Z ω)
        (integrable_const _) (hiZ.smul θ), integral_smul, hmean, smul_zero, add_zero,
      integral_smul] at hs
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul] using hs
  have hcap : M ≤ (1 + c * ‖V‖) • (1 : Matrix n n ℂ) := by
    calc
      M ≤ 1 + c • V := hle
      _ ≤ 1 + c • (‖V‖ • (1 : Matrix n n ℂ)) :=
        add_le_add_right (smul_le_smul_of_nonneg_left hVle hc) 1
      _ = _ := by module
  have hlower : Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) ≤ M := by
    have hh : ∀ᵐ ω ∂μ, Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) ≤
        NormedSpace.exp (θ • Z ω) := by
      filter_upwards [hZ, hnorm] with ω hω hωnorm
      apply exp_neg_norm_smul_one_le (hω.smul (IsSelfAdjoint.all θ))
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ] using
        mul_le_mul_of_nonneg_left hωnorm hθ
    have hi := integral_mono_ae
      (f := fun _ : Ω ↦ Real.exp (-(θ * R)) • (1 : Matrix n n ℂ))
      (g := fun ω ↦ NormedSpace.exp (θ • Z ω)) (integrable_const _) hiM hh
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, M, Function.comp_apply] using hi
  have hM : IsStrictlyPositive M :=
    (Matrix.isStrictlyPositive_iff_posDef.mpr
      ((Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef).smul (Real.exp_pos _))).of_le hlower
  have hlog := CFC.log_le_log hcap hM
  have hbpos : 0 < 1 + c * ‖V‖ := by positivity
  have hscalar : Real.log (1 + c * ‖V‖) ≤ c * ‖V‖ := by
    have hh := Real.log_le_sub_one_of_pos hbpos
    linarith
  change CFC.log M ≤ (c * ‖V‖) • (1 : Matrix n n ℂ)
  calc
    CFC.log M ≤ CFC.log ((1 + c * ‖V‖) • (1 : Matrix n n ℂ)) := hlog
    _ = Real.log (1 + c * ‖V‖) • (1 : Matrix n n ℂ) := by
      rw [← Algebra.algebraMap_eq_smul_one, CFC.log_algebraMap, Algebra.algebraMap_eq_smul_one]
    _ ≤ _ := smul_le_smul_of_nonneg_right hscalar (by positivity)

end Matrix
