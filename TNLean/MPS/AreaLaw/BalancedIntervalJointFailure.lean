/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalFailure

/-!
# Joint failure ancestry for all intervals below one root

Failure of the interval property anywhere in the actual root merge list,
or at the root itself, is covered by the same union of guarded local
failures as root failure. Thus simultaneous success on the actual tree
uses the same list of internal nodes, without an additional union over
all possible subintervals.

This is a deterministic auxiliary to the joint-success estimate in ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.
-/

namespace TNLean.MPS.AreaLaw

/-- Failure of the interval property at the root or any of its actual
listed descendants is contained in the same union of guarded local
failures over that root list. Only the valid short-leaf property is assumed.
There is no probability, long-node success or new tree hypothesis.
Auxiliary to ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem joint_failure_subset_iUnion_guardedIntervalFailure {α : Type*} {L q : ℕ}
    (operation : α → IntervalMergeOperation L q) (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    {ω | ¬(P p r (balancedIntervalSpace (operation ω) width hwidth p r) ∧
      ∀ J ∈ balancedIntervalMergeList width hwidth p r,
        P J.1 J.2 (balancedIntervalSpace (operation ω) width hwidth J.1 J.2))} ⊆
      ⋃ J ∈ balancedIntervalMergeList width hwidth p r,
        guardedIntervalFailure operation width hwidth P J := by
  classical
  intro ω hbad
  let Q := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
    P a b S ∧ ∀ J ∈ balancedIntervalMergeList width hwidth a b,
      P J.1 J.2 (balancedIntervalSpace (operation ω) width hwidth J.1 J.2)
  have hleafQ (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L) (hshort : b - a ≤ width) :
      Q a b ⊤ := by
    refine ⟨hleaf a b hab hbL hshort, ?_⟩
    intro J hJ
    rw [balancedIntervalMergeList, dite_eq_left hshort] at hJ
    cases hJ
  have hbadQ : ¬Q p r (balancedIntervalSpace (operation ω) width hwidth p r) := hbad
  obtain ⟨J, hJ, hfailure⟩ :=
    exists_guardedIntervalFailure_of_root_failure operation width hwidth Q hleafQ
      ω p r hpr hrL hbadQ
  obtain ⟨hleft, hright, hparent⟩ := hfailure
  apply Set.mem_iUnion₂.mpr
  refine ⟨J, hJ, hleft.1, hright.1, ?_⟩
  intro hparentP
  apply hparent
  refine ⟨hparentP, ?_⟩
  intro K hK
  by_cases hshort : J.2 - J.1 ≤ width
  · rw [balancedIntervalMergeList, dite_eq_left hshort] at hK
    cases hK
  · rw [balancedIntervalMergeList, dite_eq_right hshort] at hK
    simp only [List.mem_append, List.mem_singleton] at hK
    rcases hK with (hK | hK) | hK
    · exact hleft.2 K hK
    · exact hright.2 K hK
    · subst K
      exact hparentP

end TNLean.MPS.AreaLaw
