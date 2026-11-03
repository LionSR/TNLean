/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalTree

/-!
# Balanced interval spaces from actual local choices

A fixed family of candidate parent spaces and successful local choices defines
one actual merge operation. Its balanced recursion inherits the invariant at
every interval. The chosen candidate at each parent is retained explicitly.
This is a choice-based auxiliary for ALVV, arXiv:1602.08828v2, the merge
construction, lines 1662–1677, and its induction, lines 1777–1817. It asserts
neither measurable dependence on the children nor an adaptive probability.
-/

namespace TNLean.MPS.AreaLaw

/-- Successful choices for each valid pair of children construct one actual
merge operation and its balanced recursion. The candidate index is retained
in every parent equality; final viable spaces are not assumed. Supporting
ALVV, arXiv:1602.08828v2, lines 1662–1677 and 1777–1817. -/
theorem exists_balanced_interval_tree_of_choices {L q width : ℕ} (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (I : ∀ (J : LongIntervalIndex L width) (k : ℕ)
      (_hpk : J.val.1 ≤ k) (_hkr : k ≤ J.val.2),
      Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)) →
      Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q)) → Type*)
    (candidate : ∀ (J : LongIntervalIndex L width) (k : ℕ)
      (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      I J k hpk hkr S1 S2 →
        Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)))
    (hleaf : ∀ (p r : ℕ), p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (hchoice : ∀ (J : LongIntervalIndex L width) (k : ℕ)
      (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
      P J.val.1 k S1 → P k J.val.2 S2 →
      ∃ i : I J k hpk hkr S1 S2, P J.val.1 J.val.2 (candidate J k hpk hkr S1 S2 i)) :
    ∃ operation : IntervalMergeOperation L q,
      (∀ (J : LongIntervalIndex L width) (k : ℕ)
        (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
        (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
        (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q))),
        P J.val.1 k S1 → P k J.val.2 S2 →
        ∃ i : I J k hpk hkr S1 S2,
          operation J.val.1 k J.val.2 hpk hkr S1 S2 = candidate J k hpk hkr S1 S2 i ∧
          P J.val.1 J.val.2 (operation J.val.1 k J.val.2 hpk hkr S1 S2)) ∧
      ∀ (p r : ℕ), p ≤ r → r ≤ L →
        P p r (balancedIntervalSpace operation width hwidth p r) := by
  classical
  let operation : IntervalMergeOperation L q := fun p k r hpk hkr S1 S2 ↦
    if h : (p ≤ r ∧ r ≤ L ∧ width < r - p) ∧ P p k S1 ∧ P k r S2 then
      candidate ⟨(p, r), h.1⟩ k hpk hkr S1 S2
        (Classical.choose (hchoice ⟨(p, r), h.1⟩ k hpk hkr S1 S2 h.2.1 h.2.2))
    else ⊤
  have hoperation (J : LongIntervalIndex L width) (k : ℕ)
      (hpk : J.val.1 ≤ k) (hkr : k ≤ J.val.2)
      (S1 : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 k → Fin q)))
      (S2 : Submodule ℂ (EuclideanSpace ℂ (interval L k J.val.2 → Fin q)))
      (hS1 : P J.val.1 k S1) (hS2 : P k J.val.2 S2) :
      ∃ i : I J k hpk hkr S1 S2,
        operation J.val.1 k J.val.2 hpk hkr S1 S2 = candidate J k hpk hkr S1 S2 i ∧
        P J.val.1 J.val.2 (operation J.val.1 k J.val.2 hpk hkr S1 S2) := by
    let i := Classical.choose (hchoice J k hpk hkr S1 S2 hS1 hS2)
    have hi := Classical.choose_spec (hchoice J k hpk hkr S1 S2 hS1 hS2)
    have heq : operation J.val.1 k J.val.2 hpk hkr S1 S2 = candidate J k hpk hkr S1 S2 i := by
      dsimp only [operation]
      split_ifs with h
      · rfl
      · exact False.elim (h ⟨J.property, hS1, hS2⟩)
    exact ⟨i, heq, heq.symm ▸ hi⟩
  clear_value operation
  refine ⟨operation, hoperation, ?_⟩
  intro p r hpr hrL
  apply balancedIntervalSpace_invariant operation hwidth P hleaf ?_ p r hpr hrL
  intro p k r hpk hkr hrL hlong S1 S2 hS1 hS2
  let J : LongIntervalIndex L width := ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
  exact (hoperation J k hpk hkr S1 S2 hS1 hS2).choose_spec.2

end TNLean.MPS.AreaLaw
