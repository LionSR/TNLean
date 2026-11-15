/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalHistoryFailure
import QICLean.Analysis.FiniteProductUnionProbability

/-!
# One joint probability bound for retained properties and literal histories

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
