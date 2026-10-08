/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ApproximateCircuitRealAccuracy

/-!
# Fixed inverse-power accuracy meets the original gate budget

An expansion available at every fixed inverse-power accuracy can be used at
the gate-count-dependent budget of the actual density approximation. One
explicit fixed exponent suffices simultaneously for every size at least two.
The bound includes the zero-gate case through the same maximum used in the
original gate budget.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–175 and 590–600.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8769-original-sampling-approximatecircuitbudget-01
TNLean.PEPS.PairEffect.EffectCircuit.IsGateApproximation.mono
Provenance-ID: 8769-original-sampling-approximatecircuitbudget-02
TNLean.PEPS.PairEffect.EffectCircuit.isGateApproximation_budget_of_power_bound
Provenance-ID: 8769-original-sampling-approximatecircuitbudget-03
TNLean.PEPS.PairEffect.inversePower_le_sourceGateBudget_half
-/


noncomputable section
namespace TNLean.PEPS.PairEffect

/-- A fixed inverse-power local error is smaller than the actual budget that
reserves one quarter of the target physical error for approximate gates. -/
theorem inversePower_le_sourceGateBudget_half (L C p : ℝ) (M n : ℕ)
    (hL : 2 ≤ L) (hC : 1 ≤ C) (hM : (M : ℝ) ≤ C * L ^ n) :
    (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ ≤ sourceGateBudget (L ^ (-p) / 2) M := by
  have hLone : 1 ≤ L := le_trans (by norm_num) hL
  have hmax : ((max 1 M : ℕ) : ℝ) ≤ C * L ^ n := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hLone)) hM
  have he := gateApproximation_error_real_pow_le L C p (max 1 M) n hL hmax
  unfold sourceGateBudget
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

namespace EffectCircuit
variable {P : Type}

/-- Increasing the local approximation budget preserves the same original
operators and the same approximate monomial lists. -/
theorem IsGateApproximation.mono {a b : Layout P} {w : EffectCircuit a b}
    {G : w.GateMaps} {δ δ' : ℝ} (h : w.IsGateApproximation δ G) (hδ : δ ≤ δ') :
    w.IsGateApproximation δ' G := by
  induction w with
  | id => trivial
  | comp w v ihw ihv => exact ⟨ihw h.1, ihv h.2⟩
  | localMap => exact h
  | gate => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hδ⟩
  | swap => trivial
  | frame r w ih => exact ih h

/-- Original gate expansions at one fixed inverse-power precision satisfy the
actual gate-count budget for the requested real physical accuracy. The choice
of exponent depends on the uniform count bound, not on private dimensions. -/
theorem isGateApproximation_budget_of_power_bound {a b : Layout P}
    (w : EffectCircuit a b) (G : w.GateMaps) (L C p : ℝ) (M n : ℕ)
    (hL : 2 ≤ L) (hC : 1 ≤ C) (hM : (M : ℝ) ≤ C * L ^ n)
    (h : w.IsGateApproximation (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ G) :
    w.IsGateApproximation (sourceGateBudget (L ^ (-p) / 2) M) G :=
  h.mono (inversePower_le_sourceGateBudget_half L C p M n hL hC hM)

end EffectCircuit
end TNLean.PEPS.PairEffect
