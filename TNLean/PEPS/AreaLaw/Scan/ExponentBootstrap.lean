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

namespace TNLean.PEPS.AreaLaw.Scan

variable {ι : Type*} {F : ι → ℕ → ℝ}

/-- A uniform quadratic bound extends a uniform power bound valid from the scale `N` on to all
positive integer scales, with the explicit constant `C + V N²`. The constant is independent of
the family index. Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–796. -/
theorem uniform_power_bound_of_threshold_le {V e C : ℝ} (N : ℕ)
    (hV : 0 ≤ V) (he : 0 ≤ e) (hC : 0 ≤ C)
    (hvolume : ∀ i n, 1 ≤ n → F i n ≤ V * (n : ℝ) ^ 2)
    (hlarge : ∀ i n, N ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) :
    ∀ i n, 1 ≤ n → F i n ≤ (C + V * (N : ℝ) ^ 2) * (n : ℝ) ^ (1 + e) := by
  have hVN : 0 ≤ V * (N : ℝ) ^ 2 := mul_nonneg hV (sq_nonneg _)
  intro i n hn
  by_cases hlarge' : N ≤ n
  · exact (hlarge i n hlarge').trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hVN) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (lt_of_not_ge hlarge').le
    calc
      F i n ≤ V * (n : ℝ) ^ 2 := hvolume i n hn
      _ ≤ V * (N : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) hnN 2) hV
      _ ≤ C + V * (N : ℝ) ^ 2 := le_add_of_nonneg_left hC
      _ ≤ (C + V * (N : ℝ) ^ 2) * (n : ℝ) ^ (1 + e) :=
        le_mul_of_one_le_right (add_nonneg hC hVN)
          (Real.one_le_rpow (by exact_mod_cast hn) (add_nonneg zero_le_one he))

/-- A uniform quadratic bound extends a uniform large-scale power bound to all
positive integer scales. The resulting constant is independent of the family index.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–796. -/
private theorem exists_uniform_power_bound_of_eventually {V e C : ℝ}
    (hV : 0 ≤ V) (he : 0 ≤ e) (hC : 0 < C)
    (hvolume : ∀ i n, 1 ≤ n → F i n ≤ V * (n : ℝ) ^ 2)
    (hlarge : ∃ N : ℕ, ∀ i n, N ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ i n, 1 ≤ n → F i n ≤ C' * (n : ℝ) ^ (1 + e) :=
  let ⟨N, hN⟩ := hlarge
  ⟨_, add_pos_of_pos_of_nonneg hC (by positivity),
    uniform_power_bound_of_threshold_le N hV he hC.le hvolume hN⟩

/-- A uniform power bound remains valid after increasing its exponent on scales `n ≥ 1`.
Source: the final exponent comparison in `08-scanner.tex`, lines 788–803. -/
private theorem exists_uniform_power_bound_mono {e e' : ℝ} (hee' : e ≤ e')
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) :
    ∃ C : ℝ, 0 < C ∧ ∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e') := by
  obtain ⟨C, hC, hbound⟩ := hbound
  refine ⟨C, hC, fun i n hn ↦ (hbound i n hn).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (add_le_add le_rfl hee')) hC.le

/-- The number of bootstrap rounds `⌈log (ε / e₀) / log (1 - ℓ)⌉₊`: the least `m` with
`(1 - ℓ) ^ m e₀ ≤ ε` when `0 < ε`, `0 < e₀` and `0 < ℓ < 1`. Source: proof of Proposition 9.5,
`08-scanner.tex`, lines 788–803. -/
noncomputable def boxBootstrapRounds (e₀ ε ℓ : ℝ) : ℕ :=
  ⌈Real.log (ε / e₀) / Real.log (1 - ℓ)⌉₊

/-- After `boxBootstrapRounds e₀ ε ℓ` rounds the exponent `(1 - ℓ) ^ m e₀` is at most `ε`.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803. -/
theorem pow_boxBootstrapRounds_mul_le {e₀ ε ℓ : ℝ} (he₀ : 0 < e₀) (hε : 0 < ε)
    (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) :
    (1 - ℓ) ^ boxBootstrapRounds e₀ ε ℓ * e₀ ≤ ε := by
  have hθ : 0 < 1 - ℓ := sub_pos.mpr hℓ₁
  have hlog : Real.log (1 - ℓ) < 0 := Real.log_neg hθ (sub_lt_self 1 hℓ)
  have hm : (boxBootstrapRounds e₀ ε ℓ : ℝ) * Real.log (1 - ℓ) ≤ Real.log (ε / e₀) :=
    (div_le_iff_of_neg hlog).mp (Nat.le_ceil _)
  rw [← le_div_iff₀ he₀, ← Real.log_le_log_iff (pow_pos hθ _) (div_pos hε he₀),
    Real.log_pow]
  exact hm

/-- Before `boxBootstrapRounds e₀ ε ℓ` rounds the exponent `(1 - ℓ) ^ j e₀` still exceeds `ε`.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803. -/
theorem lt_pow_mul_of_lt_boxBootstrapRounds {e₀ ε ℓ : ℝ} (he₀ : 0 < e₀) (hε : 0 < ε)
    (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) {j : ℕ} (hj : j < boxBootstrapRounds e₀ ε ℓ) :
    ε < (1 - ℓ) ^ j * e₀ := by
  have hθ : 0 < 1 - ℓ := sub_pos.mpr hℓ₁
  have hlog : Real.log (1 - ℓ) < 0 := Real.log_neg hθ (sub_lt_self 1 hℓ)
  have hm : Real.log (ε / e₀) < (j : ℝ) * Real.log (1 - ℓ) :=
    (lt_div_iff_of_neg hlog).mp (Nat.lt_ceil.mp hj)
  rw [← div_lt_iff₀ he₀, ← Real.log_lt_log_iff (div_pos hε he₀) (pow_pos hθ _),
    Real.log_pow]
  exact hm

/-- One bootstrap round: an improved large-scale constant `G C` from the scale `N C` on,
extended to all positive scales by the volume bound, gives `G C + V (N C)²`. Source: proof of
Proposition 9.5, `08-scanner.tex`, lines 788–796. -/
noncomputable def boxBootstrapStep (V : ℝ) (G : ℝ → ℝ) (N : ℝ → ℕ) (C : ℝ) : ℝ :=
  G C + V * (N C : ℝ) ^ 2

/-- The bootstrap constants `C₀, C₁, …` with `C_{j+1} = G C_j + V (N C_j)²`, starting from the
initial constant `C₀`. Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803. -/
noncomputable def boxBootstrapConstant (V : ℝ) (G : ℝ → ℝ) (N : ℝ → ℕ) (C₀ : ℝ) : ℕ → ℝ
  | 0 => C₀
  | j + 1 => boxBootstrapStep V G N (boxBootstrapConstant V G N C₀ j)

/-- The bootstrap constants stay nonnegative when the initial constant, the volume coefficient and
every improved constant are. Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803. -/
theorem boxBootstrapConstant_nonneg {V C₀ : ℝ} {G : ℝ → ℝ} {N : ℝ → ℕ} (hV : 0 ≤ V)
    (hC₀ : 0 ≤ C₀) (hG : ∀ C, 0 ≤ C → 0 ≤ G C) (j : ℕ) :
    0 ≤ boxBootstrapConstant V G N C₀ j := by
  induction j with
  | zero => exact hC₀
  | succ j hj => exact add_nonneg (hG _ hj) (mul_nonneg hV (sq_nonneg _))

/-- The bootstrap constants stay positive when the initial constant and every improved constant
are positive. Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803. -/
theorem boxBootstrapConstant_pos {V C₀ : ℝ} {G : ℝ → ℝ} {N : ℝ → ℕ} (hV : 0 ≤ V)
    (hC₀ : 0 < C₀) (hG : ∀ C, 0 ≤ C → 0 < G C) (j : ℕ) :
    0 < boxBootstrapConstant V G N C₀ j := by
  induction j with
  | zero => exact hC₀
  | succ j hj => exact add_pos_of_pos_of_nonneg (hG _ hj.le) (mul_nonneg hV (sq_nonneg _))

/-- **Finite bootstrap with explicit constants.** Suppose a family has a uniform quadratic bound
`V n²` and an initial bound `C₀ n^(1 + e₀)`, and that every bound `C n^(1 + e)` at all
positive scales, with `0 ≤ C` and `ε < e ≤ e₀`, improves to `G C n^(1 + (1 - ℓ)e)` from the
scale `N C` on, where the improved constant `G C` and the scale `N C` do not depend on `e`.
Then the bound `C_m n^(1 + ε)` holds at every positive scale, where
`m = boxBootstrapRounds e₀ ε ℓ` and `C_m = boxBootstrapConstant V G N C₀ m`.
Source: proof of Proposition 9.5, `08-scanner.tex`, lines 788–803. -/
theorem uniform_power_bound_of_boxBootstrapRounds {V e₀ ε ℓ C₀ : ℝ} {G : ℝ → ℝ} {N : ℝ → ℕ}
    (hV : 0 ≤ V) (he₀ : 0 < e₀) (hε : 0 < ε) (hℓ : 0 < ℓ) (hℓ₁ : ℓ < 1) (hC₀ : 0 ≤ C₀)
    (hG : ∀ C, 0 ≤ C → 0 ≤ G C)
    (hvolume : ∀ i n, 1 ≤ n → F i n ≤ V * (n : ℝ) ^ 2)
    (hinitial : ∀ i n, 1 ≤ n → F i n ≤ C₀ * (n : ℝ) ^ (1 + e₀))
    (himprove : ∀ e C : ℝ, ε < e → e ≤ e₀ → 0 ≤ C →
      (∀ i n, 1 ≤ n → F i n ≤ C * (n : ℝ) ^ (1 + e)) →
      ∀ i n, N C ≤ n → F i n ≤ G C * (n : ℝ) ^ (1 + (1 - ℓ) * e)) :
    ∀ i n, 1 ≤ n → F i n ≤
      boxBootstrapConstant V G N C₀ (boxBootstrapRounds e₀ ε ℓ) * (n : ℝ) ^ (1 + ε) := by
  have hθ : 0 < 1 - ℓ := sub_pos.mpr hℓ₁
  have hiter : ∀ j : ℕ, j ≤ boxBootstrapRounds e₀ ε ℓ → ∀ i n, 1 ≤ n →
      F i n ≤ boxBootstrapConstant V G N C₀ j * (n : ℝ) ^ (1 + (1 - ℓ) ^ j * e₀) := by
    intro j
    induction j with
    | zero => simpa only [pow_zero, one_mul, boxBootstrapConstant] using fun _ ↦ hinitial
    | succ j hj =>
      intro hjm
      have he := lt_pow_mul_of_lt_boxBootstrapRounds he₀ hε hℓ hℓ₁ hjm
      have heupper : (1 - ℓ) ^ j * e₀ ≤ e₀ :=
        mul_le_of_le_one_left he₀.le (pow_le_one₀ hθ.le (sub_le_self 1 hℓ.le))
      have hCj := boxBootstrapConstant_nonneg (N := N) hV hC₀ hG j
      rw [pow_succ', mul_assoc]
      exact uniform_power_bound_of_threshold_le _ hV (mul_nonneg hθ.le (hε.trans he).le)
        (hG _ hCj) hvolume (himprove _ _ he heupper hCj (hj (Nat.le_of_succ_le hjm)))
  exact fun i n hn ↦ (hiter _ le_rfl i n hn).trans <| mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
      (add_le_add le_rfl (pow_boxBootstrapRounds_mul_le he₀ hε hℓ hℓ₁)))
    (boxBootstrapConstant_nonneg hV hC₀ hG _)

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
