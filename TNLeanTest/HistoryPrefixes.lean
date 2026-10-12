/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.HistoryPrefixes

/-!
# Regression tests for actual history-prefix marginals

The prefix identity applies to arbitrary events, signed observables, and empty
offset spaces. Extending a history cannot change an earlier prefix.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

example {K m M N j : ℕ} (h : History K m M N) (c : ChargeChoices K M)
    (hj : j ≤ N) :
    prefixHistory (extendHistory h c) j (hj.trans (Nat.le_succ N)) =
      prefixHistory h j hj := prefixHistory_extendHistory h c hj

example {K m M N j : ℕ} (hM : 0 < M) (hj : j ≤ N)
    (E : History K m M j → Prop) [DecidablePred E] :
    (∑ h : History K m M N, if E (prefixHistory h j hj) then historyWeight h else 0) =
      ∑ h : History K m M j, if E h then historyWeight h else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using
    sum_historyWeight_mul_prefix hM hj (fun h ↦ if E h then 1 else 0)

-- No positive-offset assumption is smuggled into the marginal identity.
example {N j : ℕ} (hj : j ≤ N) (F : History 1 0 2 j → ℝ) :
    (∑ h : History 1 0 2 N, historyWeight h * F (prefixHistory h j hj)) =
      ∑ h : History 1 0 2 j, historyWeight h * F h :=
  sum_historyWeight_mul_prefix (by decide) hj F

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Scan.prefixHistory_extendHistory'
depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prefixHistory_extendHistory

/--
info: 'TNLean.PEPS.AreaLaw.Scan.sum_historyWeight_mul_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_historyWeight_mul_prefix
