/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.QutritApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Ring

/-!
# A bounded-entropy family with no polynomial MPS approximation

The qutrit tensor-power family has uniformly bounded interval entropy, yet
its bond dimension at any fixed trace error below one eighth eventually
exceeds every polynomial in the physical length `M = 2N³`.

Source: arXiv:0705.0292v2, `paper_v2.tex`, lines 421–479.
-/

open Filter Asymptotics

namespace TNLean.MPS.AreaLaw.EntropyScaling

/-- Exponential qutrit bond growth eventually exceeds any polynomial in the
copy-family chain length. The polynomial coefficient can have either sign. -/
private theorem eventually_polynomial_lt_exponential {δ : ℝ} (hδ : δ < 1 / 8)
    (C : ℝ) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      C * (2 * (N : ℝ) ^ 3) ^ k < (2 : ℝ) ^ N * (1 - 2 * δ) + 1 := by
  have hα : 0 < 1 - 2 * δ := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo := (isLittleO_pow_exp_pos_mul_atTop (3 * k) hlog).const_mul_left
    (C * (2 : ℝ) ^ k)
  have hnat := hlo.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hnat.bound hα] with N hN
  change ‖C * (2 : ℝ) ^ k * (N : ℝ) ^ (3 * k)‖ ≤
    (1 - 2 * δ) * ‖Real.exp (Real.log 2 * (N : ℝ))‖ at hN
  have hexp : Real.exp (Real.log 2 * (N : ℝ)) = (2 : ℝ) ^ N := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hexp, Real.norm_of_nonneg (show 0 ≤ (2 : ℝ) ^ N by positivity)] at hN
  calc
    C * (2 * (N : ℝ) ^ 3) ^ k = C * (2 : ℝ) ^ k * (N : ℝ) ^ (3 * k) := by
      rw [mul_pow, ← pow_mul, mul_assoc]
    _ ≤ ‖C * (2 : ℝ) ^ k * (N : ℝ) ^ (3 * k)‖ := le_abs_self _
    _ ≤ (1 - 2 * δ) * (2 : ℝ) ^ N := hN
    _ < (2 : ℝ) ^ N * (1 - 2 * δ) + 1 := by linarith

/-- At any fixed full trace error below one eighth, every polynomial bound in
physical chain length eventually fails for actual MPS approximations.
Source: arXiv:0705.0292v2, lines 421–479. Approximants need not be normalized. -/
theorem eventually_no_polynomial_mps_approximation_qutritCopies {δ : ℝ}
    (hδ : δ < 1 / 8) (C : ℝ) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ¬ ∃ (D : ℕ)
      (φ : EuclideanSpace ℂ (Fin (N ^ 2 * (N + N)) → Fin 3)),
      IsOpenMPS (N ^ 2 * (N + N)) 3 D (fun x ↦ φ x) ∧
      (D : ℝ) ≤ C * (2 * (N : ℝ) ^ 3) ^ k ∧
      Matrix.rectangularTraceNorm
        (Matrix.euclideanOuterProduct (qutritCopies N) (qutritCopies N) -
          Matrix.euclideanOuterProduct φ φ) ≤ δ := by
  filter_upwards [eventually_polynomial_lt_exponential hδ C k,
    eventually_ge_atTop 2] with N hpoly hN
  rintro ⟨D, φ, hmps, hD, he⟩
  nlinarith [bondDimension_qutritCopies_ge hN φ hmps,
    mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (2 : ℝ) ^ N)]

end TNLean.MPS.AreaLaw.EntropyScaling
