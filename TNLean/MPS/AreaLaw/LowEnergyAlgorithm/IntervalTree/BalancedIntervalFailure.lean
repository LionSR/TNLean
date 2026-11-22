/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.BalancedIntervalTree
import QICLean.Probability.Measure.FiniteProductSectionProbability

/-!
# Failure ancestry in the actual balanced interval tree

If every short leaf satisfies a property, failure at the root implies
failure at an internal node whose two actual children satisfy the property.
Only the internal intervals descended from that root are needed. The
operation may depend arbitrarily on an external choice; no probability
or long-node hypothesis enters this deterministic argument.

This is an auxiliary to the probability estimate in ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.

## Joint failure ancestry for all intervals below one root

Failure of the interval property anywhere in the actual root merge list,
or at the root itself, is covered by the same union of guarded local
failures as root failure. Thus simultaneous success on the actual tree
uses the same list of internal nodes, without an additional union over
all possible subintervals.

This is a deterministic auxiliary to the joint-success estimate in ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817.

## One failure union for interval viability and sampling histories

A history event at a parent, together with the property of both actual children,
implies the property of that same retained parent. Failure of either the retained
property or a listed history is therefore covered by one union of guarded history
failures. Only the actual root merge list is used; no second tree is defined.

This is a conditional deterministic auxiliary to ALVV, arXiv:1602.08828v2,
resampling at lines 749–755 and `t:alg1`, lines 1777–1817. The local implication
is explicit. A later application must use the literal stopped sampling history,
not infer that history from final retained-space viability alone.

## One joint probability bound for retained properties and literal histories

Measurable guarded history failures with bounded actual coordinate sections
control simultaneous success on the same root merge list. One union suffices
for both retained-space properties and all listed histories. The coordinates
may contain finite sequences, and only independence of their product law is used.

This is a conditional analytic auxiliary to ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. Measurability, section estimates and the local
history-to-parent implication are explicit inputs, not a physical sampling
conclusion. The bound concerns outer measure, so no additional measurability
premise on the joint failure event is necessary.
-/

section

open ManyBody (interval)

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

end

section

open ManyBody (interval)

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

end

section

open ManyBody (interval)

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

end

section

open ManyBody (interval)

open MeasureTheory
open scoped ENNReal

namespace TNLean.MPS.AreaLaw

/-- True coordinate-section bounds for guarded literal-history failures
control failure of root viability or any listed retained property or history
with the same merge count. No second union or all-overlap success is assumed.
Conditional auxiliary for ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
theorem pi_balancedIntervalSpace_joint_history_failure_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ I, MeasurableSpace (Ω I)]
    (μ : ∀ I, Measure (Ω I)) [∀ I, IsProbabilityMeasure (μ I)]
    {L q : ℕ} (operation : (∀ I, Ω I) → IntervalMergeOperation L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ a b : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L a b → Fin q)) → Prop)
    (H : ℕ × ℕ → Set (∀ I, Ω I))
    (hleaf : ∀ a b : ℕ, a ≤ b → b ≤ L → b - a ≤ width → P a b ⊤)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L)
    (coordinate : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r} → ι)
    (beta : ℝ≥0∞) :
    let S := fun (a b : ℕ) (ω : ∀ I, Ω I) ↦
      balancedIntervalSpace (operation ω) width hwidth a b
    let E := fun J : ℕ × ℕ ↦
      {ω : ∀ I, Ω I | let k := J.1 + (J.2 - J.1) / 2
        P J.1 k (S J.1 k ω) ∧ P k J.2 (S k J.2 ω) ∧ ω ∉ H J}
    (∀ J ∈ balancedIntervalMergeList width hwidth p r, ∀ ω : ∀ I, Ω I,
      let k := J.1 + (J.2 - J.1) / 2
      P J.1 k (S J.1 k ω) → P k J.2 (S k J.2 ω) →
      ω ∈ H J → P J.1 J.2 (S J.1 J.2 ω)) →
    (∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      MeasurableSet (E J.val)) →
    (∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      ∀ ω : ∀ I, Ω I,
      μ (coordinate J) {u | Function.update ω (coordinate J) u ∈ E J.val} ≤ beta) →
    Measure.pi μ
      {ω | ¬(P p r (S p r ω) ∧
        ∀ J ∈ balancedIntervalMergeList width hwidth p r,
          P J.1 J.2 (S J.1 J.2 ω) ∧ ω ∈ H J)} ≤
      ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  intro S E hnode hE hsection
  apply (measure_mono (μ := Measure.pi μ)
    (joint_history_failure_subset_iUnion operation width hwidth P H hleaf
      p r hpr hrL hnode)).trans
  have hbound := Measure.pi_biUnion_list_le_of_update_sections μ
    (balancedIntervalMergeList width hwidth p r).attach coordinate
    (fun J ↦ E J.val) beta (fun J _ ↦ hE J) (fun J _ ω ↦ hsection J ω)
  have hlisted : Measure.pi μ (⋃ J ∈ balancedIntervalMergeList width hwidth p r, E J) ≤
      ((balancedIntervalMergeList width hwidth p r).length : ℝ≥0∞) * beta := by
    simpa only [List.mem_attach, Set.iUnion_true, Set.iUnion_subtype,
      List.length_attach] using hbound
  exact hlisted.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast length_balancedIntervalMergeList_le width hwidth p r) zero_le)

end TNLean.MPS.AreaLaw

end
