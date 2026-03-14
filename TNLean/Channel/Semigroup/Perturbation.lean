/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.Basic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.ODE.Gronwall

/-!
# Perturbation bound for dynamical semigroups — Wolf Lemma 7.1 and Corollary 7.1

## Main results

* `duhamel_formula` — **Lemma 7.1** (Duhamel/perturbation integral formula):
  `T'_t - T_t = ∫₀ᵗ T_{t-s} Δ T'_s ds`
  where `Δ = L' - L` is the difference of generators.

* `perturbation_bound` — **Corollary 7.1** (perturbation of generators):
  `‖T'_t - T_t‖ ≤ t · ‖Δ‖ · sup_{s∈[0,t]} ‖T_s‖ · sup_{s∈[0,t]} ‖T'_s‖`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §7.1, Lem 7.1, Cor 7.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder BigOperators NNReal
open Matrix Finset NormedSpace MeasureTheory

noncomputable section

variable {D : ℕ}

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-! ## Lemma 7.1: Duhamel formula

If `T_t = exp(tL)` and `T'_t = exp(tL')` with `Δ = L' - L`, then
`T'_t - T_t = ∫₀ᵗ T_{t-s} · Δ · T'_s ds`.

**Proof**: Define `f(s) := T_{t-s} · T'_s`. Then
`f'(s) = T_{t-s} · (L' - L) · T'_s = T_{t-s} · Δ · T'_s`,
and `T'_t - T_t = f(t) - f(0) = ∫₀ᵗ f'(s) ds`.
-/

/-- **Lemma 7.1** (Duhamel formula for matrix semigroups):
For `T_t = exp(tL)` and `T'_t = exp(tL')`:
`T'_t - T_t = ∫₀ᵗ T_{t-s} * Δ * T'_s ds` where `Δ = L' - L`.

Stated at the CLM level. The integral is a Bochner integral in the
CLM norm. -/
theorem duhamel_formula
    (L L' : Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    expSemigroupCLM L' t - expSemigroupCLM L t =
      ∫ s in Set.Icc 0 t,
        expSemigroupCLM L (t - s) * (L' - L) * expSemigroupCLM L' s := by
  sorry

/-! ## Corollary 7.1: Perturbation bound

`‖T'_t - T_t‖ ≤ t · ‖Δ‖ · sup_{s ∈ [0,t]} ‖T_s‖ · sup_{s' ∈ [0,t]} ‖T'_{s'}‖`

This follows from the Duhamel formula by taking norms and bounding the
integral using `norm_integral_le_integral_norm`.
-/

/-- **Corollary 7.1** (perturbation of generators):
The norm of the difference between two semigroups is bounded by the time
interval times the norm of the generator difference times the supremum
of the semigroup norms.

This is the main quantitative estimate: if two generators are close,
the semigroups remain close for bounded time intervals. -/
theorem perturbation_bound
    (L L' : Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖expSemigroupCLM L' t - expSemigroupCLM L t‖ ≤
      t * ‖L' - L‖ *
        (⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖) *
        (⨆ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L' s‖) := by
  sorry

/-- Simplified perturbation bound for quantum channels (where ‖T_s‖ ≤ 1 for
trace-preserving maps in the trace norm):
`‖T'_t - T_t‖ ≤ t · ‖Δ‖`. -/
theorem perturbation_bound_unit_norm
    (L L' : Matrix (Fin D) (Fin D) ℂ →L[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (t : ℝ) (ht : 0 ≤ t)
    (hT : ∀ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L s‖ ≤ 1)
    (hT' : ∀ s ∈ Set.Icc 0 t, ‖expSemigroupCLM L' s‖ ≤ 1) :
    ‖expSemigroupCLM L' t - expSemigroupCLM L t‖ ≤ t * ‖L' - L‖ := by
  sorry

end -- noncomputable section
