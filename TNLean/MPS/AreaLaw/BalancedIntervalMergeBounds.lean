/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalMergeList

/-!
# Bounds for the actual internal intervals

Every internal interval in a balanced root's merge list lies within that
root and has length greater than the leaf width. This identifies the
actual coordinates used when summing local failure probabilities for ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.
-/

namespace TNLean.MPS.AreaLaw

/-- The actual merge list contains only long subintervals of its root.
This concerns the descendants of one root, rather than all overlapping
intervals. Supporting ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem bounds_of_mem_balancedIntervalMergeList (width : ℕ) (hwidth : 1 ≤ width)
    (p r : ℕ) (hpr : p ≤ r) {J : ℕ × ℕ}
    (hJ : J ∈ balancedIntervalMergeList width hwidth p r) :
    p ≤ J.1 ∧ J.1 ≤ J.2 ∧ J.2 ≤ r ∧ width < J.2 - J.1 := by
  suffices ∀ n p r : ℕ, r - p = n → p ≤ r → ∀ J : ℕ × ℕ,
      J ∈ balancedIntervalMergeList width hwidth p r →
      p ≤ J.1 ∧ J.1 ≤ J.2 ∧ J.2 ≤ r ∧ width < J.2 - J.1 from
    this (r - p) p r rfl hpr J hJ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen hpr J hJ
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalMergeList, dite_eq_left hshort] at hJ
      exact (List.not_mem_nil hJ).elim
    · rw [balancedIntervalMergeList, dite_eq_right hshort] at hJ
      simp only [List.mem_append, List.mem_singleton] at hJ
      rcases hJ with (hJ | hJ) | rfl
      · have hleft := ih ((p + (r - p) / 2) - p) (by omega)
          p (p + (r - p) / 2) rfl (by omega) J hJ
        omega
      · have hright := ih (r - (p + (r - p) / 2)) (by omega)
          (p + (r - p) / 2) r rfl (by omega) J hJ
        omega
      · omega

end TNLean.MPS.AreaLaw
