/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BalancedIntervalMergeBounds
import TNLean.MPS.AreaLaw.BalancedIntervalFailure
import TNLean.MPS.AreaLaw.BalancedIntervalJointFailure
import TNLean.MPS.AreaLaw.IntervalSamplingChoices
import QICLean.Analysis.FiniteProductUnionProbability

/-!
# Root failure from guarded coordinate sections

Each actual internal interval determines its valid endpoint coordinate in
the fixed product of interval sampling laws. A uniform bound on the true
coordinate sections of the measurable guarded failures then bounds root
failure by the number of actual merges times that bound. The coordinate
laws may themselves be products of repeated samples; the original
product-Haar statements are special cases.

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

/-- Independent coordinate laws may be arbitrary probability measures.
Bounds for the actual guarded failure sections give their union the
actual internal-node count. Measurability and section bounds are explicit
intermediate hypotheses in this analytic auxiliary, not physical sampling
conclusions. Supporting ALVV, arXiv:1602.08828v2, Figure fig:algo1,
lines 1777–1817. -/
theorem pi_guardedIntervalFailure_union_le {L q : ℕ}
    {Ω : Fin (L + 1) × Fin (L + 1) → Type*}
    [∀ J, MeasurableSpace (Ω J)]
    (μ : ∀ J, Measure (Ω J)) [∀ J, IsProbabilityMeasure (μ J)]
    (operation : (∀ J, Ω J) → IntervalMergeOperation L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) (beta : ℝ≥0∞)
    (hE : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      MeasurableSet (guardedIntervalFailure operation width hwidth P J.val))
    (hsection : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      ∀ ω : ∀ I, Ω I,
        μ (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J)
          {u | Function.update ω (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) u ∈
            guardedIntervalFailure operation width hwidth P J.val} ≤ beta) :
    Measure.pi μ
      (⋃ J ∈ balancedIntervalMergeList width hwidth p r,
        guardedIntervalFailure operation width hwidth P J) ≤
        ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  have hbound := Measure.pi_biUnion_list_le_of_update_sections μ
    (balancedIntervalMergeList width hwidth p r).attach
    (balancedIntervalMergeCoordinate width hwidth p r hpr hrL)
    (fun J ↦ guardedIntervalFailure operation width hwidth P J.val) beta
    (fun J _ ↦ hE J) (fun J _ ω ↦ hsection J ω)
  have hlisted : Measure.pi μ
      (⋃ J ∈ balancedIntervalMergeList width hwidth p r,
        guardedIntervalFailure operation width hwidth P J) ≤
      ((balancedIntervalMergeList width hwidth p r).length : ℝ≥0∞) * beta := by
    simpa only [List.mem_attach, Set.iUnion_true, Set.iUnion_subtype,
      List.length_attach] using hbound
  exact hlisted.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast length_balancedIntervalMergeList_le width hwidth p r) zero_le)

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
  simpa only [intervalSamplingMeasure] using pi_guardedIntervalFailure_union_le
    (fun K : Fin (L + 1) × Fin (L + 1) ↦
      Matrix.rankUnitaryHaar (Fintype.card (interval L K.1.val K.2.val → Fin q)))
    operation width hwidth P p r hpr hrL beta hE hsection


/-- Guarded section estimates under arbitrary independent coordinate laws
bound true root failure. The leaf property, measurable guarded events and
true section bounds are explicit intermediate hypotheses. Analytic auxiliary
to ALVV, arXiv:1602.08828v2, Figure fig:algo1, lines 1777–1817. -/
theorem pi_balancedIntervalSpace_root_failure_le {L q : ℕ}
    {Ω : Fin (L + 1) × Fin (L + 1) → Type*}
    [∀ J, MeasurableSpace (Ω J)]
    (μ : ∀ J, Measure (Ω J)) [∀ J, IsProbabilityMeasure (μ J)]
    (operation : (∀ J, Ω J) → IntervalMergeOperation L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ p r : ℕ, p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) (beta : ℝ≥0∞)
    (hE : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      MeasurableSet (guardedIntervalFailure operation width hwidth P J.val))
    (hsection : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      ∀ ω : ∀ I, Ω I,
        μ (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J)
          {u | Function.update ω (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) u ∈
            guardedIntervalFailure operation width hwidth P J.val} ≤ beta) :
    Measure.pi μ
      {ω | ¬P p r (balancedIntervalSpace (operation ω) width hwidth p r)} ≤
        ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  exact (measure_mono (μ := Measure.pi μ)
    (root_failure_subset_iUnion_guardedIntervalFailure
      operation width hwidth P hleaf p r hpr hrL)).trans
    (pi_guardedIntervalFailure_union_le μ
      operation width hwidth P p r hpr hrL beta hE hsection)

/-- The same guarded section estimates bound simultaneous failure at the
root and its actual listed internal intervals. No union over all overlapping
intervals is used. Conditional analytic auxiliary to ALVV,
arXiv:1602.08828v2, Figure fig:algo1, lines 1777–1817. -/
theorem pi_balancedIntervalSpace_joint_failure_le {L q : ℕ}
    {Ω : Fin (L + 1) × Fin (L + 1) → Type*}
    [∀ J, MeasurableSpace (Ω J)]
    (μ : ∀ J, Measure (Ω J)) [∀ J, IsProbabilityMeasure (μ J)]
    (operation : (∀ J, Ω J) → IntervalMergeOperation L q)
    (width : ℕ) (hwidth : 1 ≤ width)
    (P : ∀ p r : ℕ, Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) → Prop)
    (hleaf : ∀ p r : ℕ, p ≤ r → r ≤ L → r - p ≤ width → P p r ⊤)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) (beta : ℝ≥0∞)
    (hE : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      MeasurableSet (guardedIntervalFailure operation width hwidth P J.val))
    (hsection : ∀ J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r},
      ∀ ω : ∀ I, Ω I,
        μ (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J)
          {u | Function.update ω (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) u ∈
            guardedIntervalFailure operation width hwidth P J.val} ≤ beta) :
    Measure.pi μ
      {ω | ¬(P p r (balancedIntervalSpace (operation ω) width hwidth p r) ∧
        ∀ J ∈ balancedIntervalMergeList width hwidth p r,
          P J.1 J.2 (balancedIntervalSpace (operation ω) width hwidth J.1 J.2))} ≤
        ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  exact (measure_mono (μ := Measure.pi μ)
    (joint_failure_subset_iUnion_guardedIntervalFailure
      operation width hwidth P hleaf p r hpr hrL)).trans
    (pi_guardedIntervalFailure_union_le μ
      operation width hwidth P p r hpr hrL beta hE hsection)

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
  simpa only [intervalSamplingMeasure] using pi_balancedIntervalSpace_root_failure_le
    (fun K : Fin (L + 1) × Fin (L + 1) ↦
      Matrix.rankUnitaryHaar (Fintype.card (interval L K.1.val K.2.val → Fin q)))
    operation width hwidth P hleaf p r hpr hrL beta hE hsection

end TNLean.MPS.AreaLaw
