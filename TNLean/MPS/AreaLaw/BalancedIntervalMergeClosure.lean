/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalMergeList

/-!
# Closure of the actual root merge list under descendants

A long interval occurs in its own internal merge list. Every internal
descendant of a listed interval is also in the original root list.
The statements use only the existing balanced merge list and introduce
no additional tree. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817.
-/

namespace TNLean.MPS.AreaLaw

/-- A long interval is the final internal node of its own merge list.
Auxiliary to ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem self_mem_balancedIntervalMergeList (width : ℕ) (hwidth : 1 ≤ width)
    (p r : ℕ) (hlong : width < r - p) :
    (p, r) ∈ balancedIntervalMergeList width hwidth p r := by
  rw [balancedIntervalMergeList, dite_eq_right (by omega : ¬r - p ≤ width)]
  simp only [List.mem_append, List.mem_singleton]
  tauto

/-- Internal descendants of an interval in the actual root list remain
in that same root list. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817. -/
theorem mem_balancedIntervalMergeList_trans (width : ℕ) (hwidth : 1 ≤ width)
    {p r : ℕ} {J K : ℕ × ℕ}
    (hJ : J ∈ balancedIntervalMergeList width hwidth p r)
    (hK : K ∈ balancedIntervalMergeList width hwidth J.1 J.2) :
    K ∈ balancedIntervalMergeList width hwidth p r := by
  suffices ∀ n p r : ℕ, r - p = n →
      ∀ J K : ℕ × ℕ, J ∈ balancedIntervalMergeList width hwidth p r →
        K ∈ balancedIntervalMergeList width hwidth J.1 J.2 →
        K ∈ balancedIntervalMergeList width hwidth p r from
    this (r - p) p r rfl J K hJ hK
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen J K hJ hK
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalMergeList, dite_eq_left hshort] at hJ
      cases hJ
    · rw [balancedIntervalMergeList, dite_eq_right hshort] at hJ ⊢
      simp only [List.mem_append, List.mem_singleton] at hJ ⊢
      rcases hJ with (hJ | hJ) | hJ
      · have hleft := ih ((p + (r - p) / 2) - p) (by omega)
          p (p + (r - p) / 2) rfl J K hJ hK
        tauto
      · have hright := ih (r - (p + (r - p) / 2)) (by omega)
          (p + (r - p) / 2) r rfl J K hJ hK
        tauto
      · subst J
        rw [balancedIntervalMergeList, dite_eq_right hshort] at hK
        simpa only [List.mem_append, List.mem_singleton] using hK

end TNLean.MPS.AreaLaw
