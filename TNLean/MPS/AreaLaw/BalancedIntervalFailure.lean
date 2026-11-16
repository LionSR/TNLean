/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalMergeList

/-!
# Failure ancestry in the actual balanced interval tree

If every short leaf satisfies a property, failure at the root implies
failure at an internal node whose two actual children satisfy the property.
Only the internal intervals descended from that root are needed. The
operation may depend arbitrarily on an external choice; no probability
or long-node hypothesis enters this deterministic argument.

This is an auxiliary to the probability estimate in ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.
-/

namespace TNLean.MPS.AreaLaw

/-- A guarded local failure: both actual midpoint children satisfy the
specified property, but their actual parent fails it. All spaces come from
the same chosen merge operation and the existing balanced recursion.
Auxiliary to ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
def guardedIntervalFailure {α : Type*} {L q : ℕ}
    (operation : α → IntervalMergeOperation L q) (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (J : ℕ × ℕ) : Set α :=
  {ω | let k := J.1 + (J.2 - J.1) / 2
    P J.1 k (balancedIntervalSpace (operation ω) width hwidth J.1 k) ∧
    P k J.2 (balancedIntervalSpace (operation ω) width hwidth k J.2) ∧
    ¬P J.1 J.2 (balancedIntervalSpace (operation ω) width hwidth J.1 J.2)}

/-- A failed root contains an actual internal descendant with guarded
local failure. No assumption is made on the merge operation at long nodes.
The list is the existing midpoint merge list descended from the specified
root, rather than a collection of all overlapping intervals. Auxiliary to
ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem exists_guardedIntervalFailure_of_root_failure {α : Type*} {L q : ℕ}
    (operation : α → IntervalMergeOperation L q) (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (ω : α) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L)
    (hbad : ¬P p r (balancedIntervalSpace (operation ω) width hwidth p r)) :
    ∃ J ∈ balancedIntervalMergeList width hwidth p r,
      ω ∈ guardedIntervalFailure operation width hwidth P J := by
  classical
  suffices ∀ n p r : ℕ, r - p = n → p ≤ r → r ≤ L →
      ¬P p r (balancedIntervalSpace (operation ω) width hwidth p r) →
      ∃ J ∈ balancedIntervalMergeList width hwidth p r,
        ω ∈ guardedIntervalFailure operation width hwidth P J from
    this (r - p) p r rfl hpr hrL hbad
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p r hlen hpr hrL hbad
    by_cases hshort : r - p ≤ width
    · rw [balancedIntervalSpace_of_short (operation ω) hwidth hshort] at hbad
      exact (hbad (hleaf p r hpr hrL hshort)).elim
    · let k := p + (r - p) / 2
      have hpk : p ≤ k := by dsimp only [k]; omega
      have hkr : k ≤ r := by dsimp only [k]; omega
      rw [balancedIntervalMergeList, dite_eq_right hshort]
      simp only [List.mem_append, List.mem_singleton]
      by_cases hleft : P p k (balancedIntervalSpace (operation ω) width hwidth p k)
      · by_cases hright : P k r (balancedIntervalSpace (operation ω) width hwidth k r)
        · refine ⟨(p, r), ?_, hleft, hright, hbad⟩
          tauto
        · obtain ⟨J, hJ, hfailure⟩ := ih (r - k) (by dsimp only [k]; omega)
            k r rfl hkr hrL hright
          refine ⟨J, ?_, hfailure⟩
          tauto
      · obtain ⟨J, hJ, hfailure⟩ := ih (k - p) (by dsimp only [k]; omega)
          p k rfl hpk (hkr.trans hrL) hleft
        refine ⟨J, ?_, hfailure⟩
        tauto

/-- Root failure is contained in the finite union of guarded local failures
at the actual internal descendants. This is purely deterministic: the leaf
property is the only invariant hypothesis, and no probability estimate or
long-node success assumption is supplied. Auxiliary to ALVV,
arXiv:1602.08828v2, lines 1777–1817. -/
theorem root_failure_subset_iUnion_guardedIntervalFailure {α : Type*} {L q : ℕ}
    (operation : α → IntervalMergeOperation L q) (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    {ω | ¬P p r (balancedIntervalSpace (operation ω) width hwidth p r)} ⊆
      ⋃ J ∈ balancedIntervalMergeList width hwidth p r,
        guardedIntervalFailure operation width hwidth P J := by
  intro ω hbad
  obtain ⟨J, hJ, hfailure⟩ :=
    exists_guardedIntervalFailure_of_root_failure operation width hwidth P hleaf ω p r hpr hrL hbad
  exact Set.mem_iUnion₂.mpr ⟨J, hJ, hfailure⟩

end TNLean.MPS.AreaLaw
