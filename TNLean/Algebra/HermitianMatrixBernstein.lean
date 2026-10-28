/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.IndependentTraceExponential
import QICLean.Analysis.TraceExponentialPerturbation

/-!
# One-sided Bernstein bounds with an upper variance bound

For independent centered Hermitian random matrices of norm at most `R`, a common
upper bound `σ2` for the individual variance norms gives the one-sided spectral
tail `d * exp (-τ² / (2mσ2 + 2Rτ/3))`. The trace-exponential estimate uses actual
independence. Exponential Markov and the scalar parameter choice, including the
zero cases, are then derived.

**Scope restriction (upper variance bound):** These are auxiliary consequences of
the Bernstein argument in Tropp, *User-friendly tail bounds for sums of random
matrices*, Theorem 6.1(ii). The conclusion uses `m * σ2`, rather than the sharper
norm of the sum of the variances for unrelated distributions. In the iid case the
actual common variance norm gives exactly the required denominator. The remaining
complex-matrix composition is recorded in
`docs/paper-gaps/finite_uniform_matrix_bernstein.tex`.

No integrability, matrix moment generating function bound or concentration
estimate is assumed as additional data. Matrices carry their canonical Borel
sigma algebra. The source is:
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open MeasureTheory

namespace Matrix

noncomputable local instance {n : Type*} [Fintype n] [DecidableEq n] :
    MeasurableSpace (Matrix n n ℂ) := borel (Matrix n n ℂ)
local instance {n : Type*} [Fintype n] [DecidableEq n] :
    BorelSpace (Matrix n n ℂ) := ⟨rfl⟩
noncomputable local instance {n : Type*} [Fintype n] [DecidableEq n] :
    NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _

/-- The trace-exponential Bernstein estimate for independent centered Hermitian
variables with a common upper bound on the individual variance norms.
This is the variance-bound consequence of the argument in Tropp, Section 6.1. -/
theorem integral_trace_exp_sum_le_bernstein_of_variance_le
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (X : Fin m → Ω → Matrix n n ℂ) (hXm : ∀ j, AEMeasurable (X j) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hHerm : ∀ j, ∀ᵐ ω ∂P, (X j ω).IsHermitian)
    (hmean : ∀ j, ∫ ω, X j ω ∂P = 0) {R θ σ2 : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3)
    (hbound : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ R)
    (hvariance : ∀ j, ‖∫ ω, X j ω ^ 2 ∂P‖ ≤ σ2) :
    (∫ ω, (NormedSpace.exp (θ • ∑ j, X j ω)).trace.re ∂P) ≤
      (Fintype.card n : ℝ) * Real.exp
        ((m : ℝ) * (θ ^ 2 / (2 * (1 - θ * R / 3))) * σ2) := by
  let c : ℝ := θ ^ 2 / (2 * (1 - θ * R / 3))
  let L : Matrix n n ℂ := ∑ j, CFC.log (∫ ω, NormedSpace.exp (θ • X j ω) ∂P)
  have hc : 0 ≤ c := by
    dsimp [c]
    apply div_nonneg (sq_nonneg θ)
    linarith
  have hθm (j : Fin m) : AEMeasurable (fun ω ↦ θ • X j ω) P := (hXm j).const_smul θ
  have hθHerm (j : Fin m) : ∀ᵐ ω ∂P, (θ • X j ω).IsHermitian :=
    (hHerm j).mono fun ω hω ↦ hω.smul (IsSelfAdjoint.all θ)
  have hθbound (j : Fin m) : ∀ᵐ ω ∂P, ‖θ • X j ω‖ ≤ θ * R := by
    filter_upwards [hbound j] with ω hω
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ] using
      mul_le_mul_of_nonneg_left hω hθ
  have hθIndep := hIndep.comp (fun _ A ↦ θ • A)
    (fun _ ↦ (continuous_id.const_smul θ).measurable)
  have hcgf := integral_trace_exp_sum_le_of_iIndepFun (fun j ω ↦ θ • X j ω)
    hθm hθIndep hθHerm hθbound isHermitian_zero
  have hlog (j : Fin m) : CFC.log (∫ ω, NormedSpace.exp (θ • X j ω) ∂P) ≤
      (c * σ2) • (1 : Matrix n n ℂ) := by
    have hj := log_integral_exp_le_bernstein (hXm j).aestronglyMeasurable (hHerm j)
      (hmean j) hR hθ hθR (hbound j)
    exact hj.trans (smul_le_smul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hvariance j) hc) (by positivity))
  have hL : L ≤ ((m : ℝ) * c * σ2) • (1 : Matrix n n ℂ) := by
    calc
      L ≤ ∑ _j : Fin m, (c * σ2) • (1 : Matrix n n ℂ) :=
        Finset.sum_le_sum fun j _ ↦ hlog j
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        ring_nf
  have hLherm : L.IsHermitian :=
    (isSelfAdjoint_sum Finset.univ fun _ _ ↦ IsSelfAdjoint.log).isHermitian
  have ht := hLherm.re_trace_exp_le
    (isHermitian_one.smul (IsSelfAdjoint.all ((m : ℝ) * c * σ2))) hL
  calc
    _ ≤ (NormedSpace.exp L).trace.re := by
      simpa only [zero_add, Finset.smul_sum, L] using hcgf
    _ ≤ (NormedSpace.exp (((m : ℝ) * c * σ2) • (1 : Matrix n n ℂ))).trace.re := ht
    _ = _ := by
      rw [← zero_add (((m : ℝ) * c * σ2) • (1 : Matrix n n ℂ)), exp_add_smul_one]
      simp only [NormedSpace.exp_zero, trace_smul, trace_one, Complex.real_smul,
        Complex.re_ofReal_mul, Complex.natCast_re]
      exact mul_comm _ _


private theorem exp_le_trace_exp_of_spectrum
    {n : Type*} [Fintype n] [DecidableEq n]
    {S : Matrix n n ℂ} (hS : S.IsHermitian) {x τ θ : ℝ}
    (hx : x ∈ spectrum ℝ S) (hτ : τ ≤ x) (hθ : 0 ≤ θ) :
    Real.exp (θ * τ) ≤ (NormedSpace.exp (θ • S)).trace.re := by
  obtain ⟨i, rfl⟩ := hS.spectrum_real_eq_range_eigenvalues ▸ hx
  have heq : (NormedSpace.exp (θ • S)).trace.re =
      ∑ j, Real.exp (θ * hS.eigenvalues j) := by
    rw [← CFC.real_exp_eq_normedSpace_exp ((hS.smul (IsSelfAdjoint.all θ)).isSelfAdjoint),
      ← cfc_comp_const_mul θ Real.exp S (ha := hS.isSelfAdjoint), hS.cfc_eq]
    exact hS.trace_cfc_eq_sum_re (fun x ↦ Real.exp (θ * x))
  rw [heq]
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ hθ)).trans
    (Finset.single_le_sum (f := fun j ↦ Real.exp (θ * hS.eigenvalues j))
      (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i))

/-- Exponential Markov for the actual upper spectral event on an arbitrary
probability space, combined with the variance-sensitive exponential estimate.
This is the parameter form of the argument for Tropp, Theorem 6.1(ii). -/
theorem probability_spectral_tail_le_bernstein_parameter
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (X : Fin m → Ω → Matrix n n ℂ) (hXm : ∀ j, AEMeasurable (X j) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hHerm : ∀ j, ∀ᵐ ω ∂P, (X j ω).IsHermitian)
    (hmean : ∀ j, ∫ ω, X j ω ∂P = 0) {R θ τ σ2 : ℝ}
    (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3)
    (hbound : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ R)
    (hvariance : ∀ j, ‖∫ ω, X j ω ^ 2 ∂P‖ ≤ σ2) :
    P.real {ω | ∃ x ∈ spectrum ℝ (∑ j, X j ω), τ ≤ x} ≤
      (Fintype.card n : ℝ) * Real.exp
        (-θ * τ + (m : ℝ) * (θ ^ 2 / (2 * (1 - θ * R / 3))) * σ2) := by
  let f (ω : Ω) : ℝ := (NormedSpace.exp (θ • ∑ j, X j ω)).trace.re
  let A : Set Ω := {ω | ∃ x ∈ spectrum ℝ (∑ j, X j ω), τ ≤ x}
  let B : Set Ω := {ω | Real.exp (θ * τ) ≤ f ω}
  have hSumHerm : ∀ᵐ ω ∂P, (∑ j, X j ω).IsHermitian := by
    filter_upwards [ae_all_iff.mpr hHerm] with ω hω
    exact (isSelfAdjoint_sum Finset.univ fun j _ ↦ (hω j).isSelfAdjoint).isHermitian
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ f ω := hSumHerm.mono fun ω hω ↦
    (hω.smul (IsSelfAdjoint.all θ)).re_trace_exp_nonneg
  have hθm (j : Fin m) : AEMeasurable (fun ω ↦ θ • X j ω) P := (hXm j).const_smul θ
  have hθbound (j : Fin m) : ∀ᵐ ω ∂P, ‖θ • X j ω‖ ≤ θ * R := by
    filter_upwards [hbound j] with ω hω
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ] using
      mul_le_mul_of_nonneg_left hω hθ
  have hi : Integrable f P := by
    have hh := integrable_trace_exp_sum_of_ae_norm_le (fun j ω ↦ θ • X j ω)
      hθm hθbound 0
    simpa only [zero_add, Finset.smul_sum, f] using hh
  have hAB : A ≤ᵐ[P] B := by
    filter_upwards [hSumHerm] with ω hω
    intro hA
    obtain ⟨x, hx, hτ⟩ := hA
    exact exp_le_trace_exp_of_spectrum hω hx hτ hθ
  have hReal : P.real A ≤ P.real B :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hAB)
  have hMarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hi (Real.exp (θ * τ))
  have hmgf := integral_trace_exp_sum_le_bernstein_of_variance_le X hXm hIndep hHerm hmean
    hR hθ hθR hbound hvariance
  have hmain : P.real A * Real.exp (θ * τ) ≤
      (Fintype.card n : ℝ) * Real.exp
        ((m : ℝ) * (θ ^ 2 / (2 * (1 - θ * R / 3))) * σ2) := by
    calc
      _ ≤ P.real B * Real.exp (θ * τ) :=
        mul_le_mul_of_nonneg_right hReal (Real.exp_pos _).le
      _ ≤ ∫ ω, f ω ∂P := by simpa only [mul_comm] using hMarkov
      _ ≤ _ := hmgf
  have hq := (le_div_iff₀ (Real.exp_pos (θ * τ))).mpr hmain
  calc
    _ ≤ _ := hq
    _ = _ := by rw [Real.exp_add, neg_mul, Real.exp_neg]; ring

private theorem exists_bernstein_parameter {v R τ : ℝ}
    (hv : 0 ≤ v) (hR : 0 ≤ R) (hτ : 0 ≤ τ) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ * R < 3 ∧
      -θ * τ + (θ ^ 2 / (2 * (1 - θ * R / 3))) * v =
        -(τ ^ 2) / (2 * v + 2 * R * τ / 3) := by
  by_cases hvp : 0 < v
  · have hden : 0 < v + R * τ / 3 := by positivity
    have hsmall : τ / (v + R * τ / 3) * R < 3 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    refine ⟨τ / (v + R * τ / 3), div_nonneg hτ hden.le, hsmall, ?_⟩
    have hone : 1 - τ / (v + R * τ / 3) * R / 3 ≠ 0 := by linarith
    have hd2 : 2 * v + 2 * R * τ / 3 ≠ 0 := by positivity
    field_simp
    ring
  · have hv0 : v = 0 := le_antisymm (le_of_not_gt hvp) hv
    by_cases hrt : 0 < R * τ
    · have hRp : 0 < R := by nlinarith
      have hτp : 0 < τ := by nlinarith
      refine ⟨3 / (2 * R), by positivity, ?_, ?_⟩
      · rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * R)]
        linarith
      · rw [hv0, mul_zero, add_zero, mul_zero, zero_add]
        field_simp
    · have hrt0 : R * τ = 0 := le_antisymm (le_of_not_gt hrt) (mul_nonneg hR hτ)
      refine ⟨0, le_rfl, by norm_num, ?_⟩
      have hden : 2 * R * τ / 3 = 0 := by
        calc
          _ = (2 : ℝ) * (R * τ) / 3 := by ring
          _ = 0 := by rw [hrt0]; norm_num
      simp [hv0, hden]

/-- One-sided Hermitian Bernstein on an arbitrary probability space with an upper
bound on every individual variance norm. The parameter choice includes zero
variance, threshold and sample count. This is a consequence of Tropp, Theorem 6.1(ii). -/
theorem probability_hermitian_bernstein_of_variance_le
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (X : Fin m → Ω → Matrix n n ℂ) (hXm : ∀ j, AEMeasurable (X j) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hHerm : ∀ j, ∀ᵐ ω ∂P, (X j ω).IsHermitian)
    (hmean : ∀ j, ∫ ω, X j ω ∂P = 0) {R τ σ2 : ℝ}
    (hR : 0 ≤ R) (hτ : 0 ≤ τ) (hσ : 0 ≤ σ2)
    (hbound : ∀ j, ∀ᵐ ω ∂P, ‖X j ω‖ ≤ R)
    (hvariance : ∀ j, ‖∫ ω, X j ω ^ 2 ∂P‖ ≤ σ2) :
    P.real {ω | ∃ x ∈ spectrum ℝ (∑ j, X j ω), τ ≤ x} ≤
      (Fintype.card n : ℝ) * Real.exp (-(τ ^ 2) / (2 * (m : ℝ) * σ2 + 2 * R * τ / 3)) := by
  obtain ⟨θ, hθ, hθR, hid⟩ :=
    exists_bernstein_parameter (mul_nonneg (Nat.cast_nonneg m) hσ) hR hτ
  have ht := probability_spectral_tail_le_bernstein_parameter (τ := τ) X hXm hIndep hHerm
    hmean hR hθ hθR hbound hvariance
  have heq : -θ * τ + (m : ℝ) * (θ ^ 2 / (2 * (1 - θ * R / 3))) * σ2 =
      -(τ ^ 2) / (2 * (m : ℝ) * σ2 + 2 * R * τ / 3) := by
    convert hid using 1 <;> ring
  simpa only [heq] using ht

end Matrix
