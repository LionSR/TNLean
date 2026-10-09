/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.OffsetDilution

/-!
# Marginals of actual finite history prefixes

Restricting a complete history preserves its offsets and the first prescribed
number of charge coordinates. Summing the unused independent coordinates gives
exactly the classical weight of that prefix. The result holds for arbitrary
real observables, without a sign assumption or a separate measure certificate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–154 and 286–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

/-- The actual initial offsets and first `j` charge choices of a complete history. -/
def prefixHistory {K m M N : ℕ} (h : History K m M N) (j : ℕ) (hj : j ≤ N) :
    History K m M j :=
  (h.1, fun t ↦ h.2 (Fin.castLE hj t))

@[simp]
theorem prefixHistory_self {K m M N : ℕ} (h : History K m M N) :
    prefixHistory h N le_rfl = h := rfl

/-- Appending a later charge does not change any already available prefix. -/
theorem prefixHistory_extendHistory {K m M N j : ℕ} (h : History K m M N)
    (c : ChargeChoices K M) (hj : j ≤ N) :
    prefixHistory (extendHistory h c) j (hj.trans (Nat.le_succ N)) =
      prefixHistory h j hj := by
  apply Prod.ext
  · rfl
  · funext t
    exact Fin.snoc_castSucc (α := fun _ ↦ ChargeChoices K M) c h.2 (Fin.castLE hj t)

/-- Every real observable of a prefix has the same expectation in the longer
actual history space. Only the side-and-slot distribution must be nonempty;
empty offset spaces contribute zero on both sides. `08-scanner.tex`, lines 145–154. -/
theorem sum_historyWeight_mul_prefix {K m M N j : ℕ} (hM : 0 < M) (hj : j ≤ N)
    (F : History K m M j → ℝ) :
    (∑ h : History K m M N, historyWeight h * F (prefixHistory h j hj)) =
      ∑ h : History K m M j, historyWeight h * F h := by
  induction N, hj using Nat.le_induction with
  | base => simp
  | succ N hj ih =>
    rw [sum_historyWeight_mul_eq_sum_extendHistory]
    simp_rw [prefixHistory_extendHistory (hj := hj)]
    calc
      _ = ∑ h : History K m M N, historyWeight h * F (prefixHistory h j hj) := by
        apply Finset.sum_congr rfl
        intro h _
        calc
          _ = (historyWeight h * F (prefixHistory h j hj)) *
              ∑ c : ChargeChoices K M, chargeWeight c := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _
            ring
          _ = historyWeight h * F (prefixHistory h j hj) := by
            rw [sum_chargeWeight K hM, mul_one]
      _ = _ := ih

end TNLean.PEPS.AreaLaw.Scan
