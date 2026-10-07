/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapParameters
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite improvement of a uniform entropy exponent

Suppose a family of quantities has a uniform quadratic bound and an initial
bound of order `r^(1 + e₀)`. If each exponent `e > ε` can be replaced
by `(1 - ℓ)e` at all sufficiently large scales, with constants and thresholds
uniform over the family, then finitely many repetitions give a uniform bound
of order `r^(1 + ε)` at every positive integer scale.

The quadratic bound absorbs the finitely many excluded scales at each step.
The exponent improvement is a hypothesis: the analytic estimate required for
the safe-box entropy is a separate result.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, proof of Proposition 9.5, `prop:small-box`,
`08-scanner.tex`, lines 788–803.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026, OpenAI, A two-dimensional area law from a global spectral gap.
Manuscript section: 08-scanner.tex.
Labels: prop:small-box; scanner:bootstrap-parameters; scanner:bootstrap-energy.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8756-tnlean.peps.arealaw.scan.exists_uniform_boxerror_bound_of_eventual_improvement
Downstream declaration:
TNLean.PEPS.AreaLaw.Scan.exists_uniform_boxError_bound_of_eventual_improvement
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {ι : Type*} {F : ι → ℕ → ℝ}

/-- A uniform quadratic bound extends a uniform large-scale power bound to all
positive integer scales. The resulting constant is independent of the family index.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–796. -/
private theorem exists_uniform_power_bound_of_eventually {V e C : ℝ}
    (hV : 0 ≤ V) (he : 0 ≤ e) (hC : 0 < C)
    (hvolume : ∀ i n, 1 ≤ n → F i n ≤ V * (n : ℝ) ^ 2)
    (hlarge : ∃ N : ℕ, ∀ i n, N ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ i n, 1 ≤ n → F i n ≤ C' * (n : ℝ) ^ (1 + e) := by
  obtain ⟨N, hN⟩ := hlarge
  have hVN : 0 ≤ V * (N : ℝ) ^ 2 := mul_nonneg hV (sq_nonneg _)
  refine ⟨C + V * (N : ℝ) ^ 2, add_pos_of_pos_of_nonneg hC hVN, ?_⟩
  intro i n hn
  by_cases hlarge : N ≤ n
  · exact (hN i n hlarge).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hVN) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (lt_of_not_ge hlarge).le
    calc
      F i n ≤ V * (n : ℝ) ^ 2 := hvolume i n hn
      _ ≤ V * (N : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) hnN 2) hV
      _ ≤ C + V * (N : ℝ) ^ 2 := le_add_of_nonneg_left hC.le
      _ ≤ (C + V * (N : ℝ) ^ 2) * (n : ℝ) ^ (1 + e) :=
        le_mul_of_one_le_right (add_nonneg hC.le hVN)
          (Real.one_le_rpow (by exact_mod_cast hn) (add_nonneg zero_le_one he))

/-- A uniform power bound remains valid after increasing its exponent on scales `n ≥ 1`.
Source: the final exponent comparison in `08-scanner.tex`, lines 788–803. -/
private theorem exists_uniform_power_bound_mono {e e' : ℝ} (hee' : e ≤ e')
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e') := by
  obtain ⟨C, hC, hbound⟩ := hbound
  refine ⟨C, hC, fun i n hn ↦ (hbound i n hn).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (add_le_add le_rfl hee')) hC.le

/-- An eventual improvement `e ↦ (1 - ℓ)e`, uniform over the family,
reaches any prescribed positive exponent after finitely many repetitions. All
bounded scales are included using the uniform quadratic estimate.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803.
The one-step improvement is assumed here; this is the finite iteration argument. -/
private theorem exists_uniform_power_bound_of_eventual_improvement {V e₀ ε ℓ : ℝ}
    (hV : 0 ≤ V) (he₀ : 0 < e₀) (hε : 0 < ε) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1)
    (hvolume : ∀ i n, 1 ≤ n → F i n ≤ V * (n : ℝ) ^ 2)
    (hinitial : ∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e₀))
    (himprove : ∀ e : ℝ, ε < e → e ≤ e₀ →
      (∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) →
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
        ∀ i n, N ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + (1 - ℓ) * e)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + ε) := by
  by_contra hfinal
  have hfactor : 0 < 1 - ℓ := sub_pos.mpr hℓ₁
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hε he₀) (sub_lt_self 1 hℓ)
  have hiter : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + (1 - ℓ) ^ j * e₀) := by
    intro j
    induction j with
    | zero => simpa only [pow_zero, one_mul] using hinitial
    | succ j hj =>
      have he : ε < (1 - ℓ) ^ j * e₀ := lt_of_not_ge fun hle ↦
        hfinal (exists_uniform_power_bound_mono hle hj)
      have heupper : (1 - ℓ) ^ j * e₀ ≤ e₀ :=
        mul_le_of_le_one_left he₀.le (pow_le_one₀ hfactor.le (sub_le_self 1 hℓ.le))
      obtain ⟨C, hC, hlarge⟩ := himprove _ he heupper hj
      simpa only [pow_succ', mul_assoc] using
        exists_uniform_power_bound_of_eventually hV
          (mul_nonneg hfactor.le (hε.trans he).le) hC hvolume hlarge
  exact hfinal (exists_uniform_power_bound_mono ((lt_div_iff₀ he₀).mp hm).le (hiter m))

/-- Conditional finite improvement to the safe-box exponent `e_* = 2 · 10⁻⁶`.
The family has a uniform quadratic bound and a uniform initial exponent
`0 < e₀ < 1`. At every intermediate exponent `e_* < e ≤ e₀`, assume a
uniform large-scale improvement to `(1 - ℓ)e`, with the single fixed choice
`ℓ = (1 - e₀) / 200000`. Then one constant bounds the whole family by
`C r^(1 + e_*)` at every positive integer scale, including the bounded scales.
Source: proof of Proposition 9.5, `prop:small-box`, `08-scanner.tex`, lines 693–803.
This theorem proves the finite iteration; its one-step entropy estimate remains a hypothesis. -/
theorem exists_uniform_boxError_bound_of_eventual_improvement {V e₀ : ℝ}
    (hV : 0 ≤ V) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1)
    (hvolume : ∀ i n, 1 ≤ n → F i n ≤ V * (n : ℝ) ^ 2)
    (hinitial : ∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e₀))
    (himprove : ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      (∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) →
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
        ∀ i n, N ≤ n → F i n ≤
          C * (n : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) := by
  obtain ⟨_, _, hℓ, hℓ₁, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  exact exists_uniform_power_bound_of_eventual_improvement hV he₀
    (by norm_num [Exponents.boxError]) hℓ hℓ₁ hvolume hinitial himprove

end TNLean.PEPS.AreaLaw.Scan
