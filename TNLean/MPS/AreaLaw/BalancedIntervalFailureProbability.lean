/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalMergeBounds
import TNLean.MPS.AreaLaw.BalancedIntervalFailure
import TNLean.MPS.AreaLaw.IntervalSamplingChoices
import QICLean.Analysis.FiniteProductUnionProbability

/-!
# Root failure from guarded coordinate sections

Each actual internal interval determines its valid endpoint coordinate in
the fixed product of interval sampling laws. A uniform bound on the true
coordinate sections of the measurable guarded failures then bounds root
failure by the number of actual merges times that bound.

This is a conditional measure-theoretic auxiliary to ALVV,
arXiv:1602.08828v2, Figure `fig:algo1` and lines 1777–1817. The section
bounds and measurability of the listed guarded events are explicit
premises. They are not asserted here for a physical sampled operation.
-/

open MeasureTheory
open scoped ENNReal

namespace TNLean.MPS.AreaLaw

/-- Every listed descendant has its actual finite endpoint coordinate.
No endpoint is clamped or assigned a value outside the valid root.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
def balancedIntervalMergeCoordinate {L : ℕ} (width : ℕ) (hwidth : 1 ≤ width)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L)
    (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r}) :
    Fin (L + 1) × Fin (L + 1) :=
  let hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
  (⟨J.val.1, Nat.lt_succ_of_le (hb.2.1.trans (hb.2.2.1.trans hrL))⟩,
    ⟨J.val.2, Nat.lt_succ_of_le (hb.2.2.1.trans hrL)⟩)

/-- Uniform true update-section bounds for the actual listed guarded
failures bound the measure of their union by the actual merge count.
No leaf invariant is needed for this conditional measure auxiliary.
Neither long-node success nor physical section estimates are asserted.
Supporting ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem intervalSamplingMeasure_guarded_failure_union_le {L q : ℕ}
    (operation : IntervalSamplingChoices L q → IntervalMergeOperation L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) (beta : ℝ≥0∞)
    (hE : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      MeasurableSet (guardedIntervalFailure operation width hwidth P J.val))
    (hsection : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      ∀ ω : IntervalSamplingChoices L q,
        Matrix.rankUnitaryHaar (Fintype.card (interval L J.val.1 J.val.2 → Fin q))
          {u | Function.update ω (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) u ∈
            guardedIntervalFailure operation width hwidth P J.val} ≤ beta) :
    intervalSamplingMeasure L q
      (⋃ J ∈ balancedIntervalMergeList width hwidth p r,
        guardedIntervalFailure operation width hwidth P J) ≤
        ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  let l := balancedIntervalMergeList width hwidth p r
  let coordinate := balancedIntervalMergeCoordinate width hwidth p r hpr hrL
  let E := fun J : {J : ℕ × ℕ // J ∈ l} ↦
    guardedIntervalFailure operation width hwidth P J.val
  have hbound := Measure.pi_biUnion_list_le_of_update_sections
    (fun K : Fin (L + 1) × Fin (L + 1) ↦
      Matrix.rankUnitaryHaar (Fintype.card (interval L K.1.val K.2.val → Fin q)))
    l.attach coordinate E beta (fun J _ ↦ hE J) (fun J _ ω ↦ hsection J ω)
  have hsubset :
      (⋃ J ∈ l, guardedIntervalFailure operation width hwidth P J) ⊆
        ⋃ J ∈ l.attach, E J := by
    intro ω hfailure
    obtain ⟨J, hJ, hfail⟩ := Set.mem_iUnion₂.mp hfailure
    exact Set.mem_iUnion₂.mpr ⟨⟨J, hJ⟩, by simp, hfail⟩
  calc
    _ ≤ intervalSamplingMeasure L q (⋃ J ∈ l.attach, E J) := measure_mono hsubset
    _ ≤ (l.length : ℝ≥0∞) * beta := by
      simpa only [intervalSamplingMeasure, List.length_attach] using hbound
    _ ≤ _ := by
      apply mul_le_mul_left
      exact_mod_cast length_balancedIntervalMergeList_le width hwidth p r

/-- The guarded-union bound and failure ancestry bound true root failure.
The valid short-leaf property is the only recursive invariant supplied;
listed measurability and true section bounds remain explicit premises.
This is a conditional auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817, not a physical sampling theorem. -/
theorem intervalSamplingMeasure_root_failure_le {L q : ℕ}
    (operation : IntervalSamplingChoices L q → IntervalMergeOperation L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ p r : ℕ, p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) (beta : ℝ≥0∞)
    (hE : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      MeasurableSet (guardedIntervalFailure operation width hwidth P J.val))
    (hsection : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      ∀ ω : IntervalSamplingChoices L q,
        Matrix.rankUnitaryHaar (Fintype.card (interval L J.val.1 J.val.2 → Fin q))
          {u | Function.update ω (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) u ∈
            guardedIntervalFailure operation width hwidth P J.val} ≤ beta) :
    intervalSamplingMeasure L q
      {ω | ¬P p r (balancedIntervalSpace (operation ω) width hwidth p r)} ≤
        ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  exact (measure_mono (root_failure_subset_iUnion_guardedIntervalFailure
    operation width hwidth P hleaf p r hpr hrL)).trans
    (intervalSamplingMeasure_guarded_failure_union_le
      operation width hwidth P p r hpr hrL beta hE hsection)

end TNLean.MPS.AreaLaw
