/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalTree

/-!
# The internal intervals of the balanced recursion

Only the internal intervals descended from the specified root are listed.
Each parent follows its two child lists, in the same midpoint subdivision
as `balancedIntervalSpace`. This supplies the finite collection of merges
for the probability estimate in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817.
-/

namespace TNLean.MPS.AreaLaw

/-- The internal intervals of the actual midpoint recursion, with each
parent following its descendants. Short leaves contribute no merge.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
def balancedIntervalMergeList (width : ℕ) (hwidth : 1 ≤ width) (p r : ℕ) :
    List (ℕ × ℕ) :=
  if _hshort : r - p ≤ width then [] else
    let k := p + (r - p) / 2
    balancedIntervalMergeList width hwidth p k ++
      balancedIntervalMergeList width hwidth k r ++ [(p, r)]
termination_by r - p
decreasing_by all_goals omega

/-- The actual root hierarchy has at most one fewer merge than sites.
This counts only descendants of the specified root, not all overlapping
intervals. Supporting ALVV, arXiv:1602.08828v2, lines 1797–1817. -/
theorem length_balancedIntervalMergeList_le (width : ℕ) (hwidth : 1 ≤ width)
    (p r : ℕ) :
    (balancedIntervalMergeList width hwidth p r).length ≤ r - p - 1 := by
  suffices ∀ n p r : ℕ, r - p = n →
      (balancedIntervalMergeList width hwidth p r).length ≤ r - p - 1 from
    this (r - p) p r rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalMergeList, dite_eq_left hshort]
      exact Nat.zero_le _
    · rw [balancedIntervalMergeList, dite_eq_right hshort]
      simp only [List.length_append, List.length_singleton]
      have hleft := ih ((p + (r - p) / 2) - p) (by omega) p (p + (r - p) / 2) rfl
      have hright := ih (r - (p + (r - p) / 2)) (by omega) (p + (r - p) / 2) r rfl
      omega

end TNLean.MPS.AreaLaw
