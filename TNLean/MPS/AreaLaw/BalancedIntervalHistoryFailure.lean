/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalJointFailure
import TNLean.MPS.AreaLaw.BalancedIntervalMergeBounds

/-!
# One failure union for interval viability and sampling histories

A history event at a parent, together with the property of both actual children,
implies the property of that same retained parent. Failure of either the retained
property or a listed history is therefore covered by one union of guarded history
failures. Only the actual root merge list is used; no second tree is defined.

This is a conditional deterministic auxiliary to ALVV, arXiv:1602.08828v2,
resampling at lines 749–755 and `t:alg1`, lines 1777–1817. The local implication
is explicit. A later application must use the literal stopped sampling history,
not infer that history from final retained-space viability alone.
-/

namespace TNLean.MPS.AreaLaw

/-- Simultaneous failure of the retained property or a literal listed history
lies in the same guarded-history union. The parent implication is required
only at the listed intervals. No probability or all-overlap invariant is
assumed. Conditional auxiliary for ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
theorem joint_history_failure_subset_iUnion {α : Type*} {L q : ℕ}
    (operation : α → IntervalMergeOperation L q) (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ a b : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L a b → Fin q)) → Prop)
    (H : ℕ × ℕ → Set α)
    (hleaf : ∀ a b : ℕ, a ≤ b → b ≤ L → b - a ≤ width → P a b ⊤)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := fun (a b : ℕ) (ω : α) ↦
      balancedIntervalSpace (operation ω) width hwidth a b
    (∀ J ∈ balancedIntervalMergeList width hwidth p r, ∀ ω : α,
      let k := J.1 + (J.2 - J.1) / 2
      P J.1 k (S J.1 k ω) → P k J.2 (S k J.2 ω) →
      ω ∈ H J → P J.1 J.2 (S J.1 J.2 ω)) →
    {ω | ¬(P p r (S p r ω) ∧
      ∀ J ∈ balancedIntervalMergeList width hwidth p r,
        P J.1 J.2 (S J.1 J.2 ω) ∧ ω ∈ H J)} ⊆
      ⋃ J ∈ balancedIntervalMergeList width hwidth p r,
        {ω | let k := J.1 + (J.2 - J.1) / 2
          P J.1 k (S J.1 k ω) ∧ P k J.2 (S k J.2 ω) ∧ ω ∉ H J} := by
  classical
  intro S hnode ω hbad
  by_contra hnot
  let Q := fun (a b : ℕ) (W : Submodule ℂ
    (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
    P a b W ∧ (width < b - a → ω ∈ H (a, b))
  have hleafQ (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L) (hshort : b - a ≤ width) :
      Q a b ⊤ :=
    ⟨hleaf a b hab hbL hshort, fun hlong ↦ False.elim ((not_lt_of_ge hshort) hlong)⟩
  have hQ : Q p r (S p r ω) ∧
      ∀ J ∈ balancedIntervalMergeList width hwidth p r,
        Q J.1 J.2 (S J.1 J.2 ω) := by
    by_contra hbadQ
    have hfailure := (joint_failure_subset_iUnion_guardedIntervalFailure
      operation width hwidth Q hleafQ p r hpr hrL) hbadQ
    obtain ⟨J, hJ, hleft, hright, hparent⟩ := Set.mem_iUnion₂.mp hfailure
    have hH : ω ∈ H J := by
      by_contra hNH
      exact hnot (Set.mem_iUnion₂.mpr ⟨J, hJ, hleft.1, hright.1, hNH⟩)
    exact hparent ⟨hnode J hJ ω hleft.1 hright.1 hH, fun _ ↦ hH⟩
  apply hbad
  refine ⟨hQ.1.1, ?_⟩
  intro J hJ
  have hlong := (bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr hJ).2.2.2
  exact ⟨(hQ.2 J hJ).1, (hQ.2 J hJ).2 hlong⟩

end TNLean.MPS.AreaLaw
