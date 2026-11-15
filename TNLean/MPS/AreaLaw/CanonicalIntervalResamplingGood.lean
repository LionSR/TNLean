/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalRawHistory

/-!
# The actual joint success event of the repeated-sampling tree

The event records original-target viability at the actual root and listed
parents, together with each listed parent's literal stopped history. It is
the success event whose complement is bounded by the existing joint-history
probability theorem. No soft-target intersection or extra success condition
is introduced.

The original target and all families and scalar parameters are fixed before
the finite sequences. Measurability follows from the existing actual retained
space and history events, followed by a countable intersection over the long
interval index. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and the balanced construction at lines 1777–1817.
-/

open MeasureTheory

namespace TNLean.MPS.AreaLaw

/-- The exact actual root-and-listed-parent success event: retained original-
target viability and the same original-target stopped histories. Its complement
is the joint failure event of the repeated-sampling tree. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
noncomputable def canonicalIntervalResamplingGood {L q width : ℕ}
    (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (p r : ℕ) :
    Set (IntervalResamplingChoices L q rounds) :=
  let S := fun (a b : ℕ) (U : IntervalResamplingChoices L q rounds) ↦
    balancedIntervalSpace (canonicalIntervalResamplingOperation
      D rounds threshold N F xi U) width hwidth a b
  {U | Submodule.IsViable (3 / 200 : ℝ) (S p r U)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
    ∀ J : LongIntervalIndex L width,
      J.val ∈ balancedIntervalMergeList width hwidth p r →
      Submodule.IsViable (3 / 200 : ℝ) (S J.val.1 J.val.2 U)
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) ∧
        U ∈ canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J}

/-- The same concrete joint success event is measurable. Countability of the
long interval index suffices; no finite enumeration, measurable basis selection
or probability-success hypothesis is required. Supporting ALVV,
arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem measurableSet_canonicalIntervalResamplingGood {L q width : ℕ}
    (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    MeasurableSet (canonicalIntervalResamplingGood D rounds hwidth threshold N F xi G p r) := by
  classical
  let S := fun (a b : ℕ) (U : IntervalResamplingChoices L q rounds) ↦
    balancedIntervalSpace (canonicalIntervalResamplingOperation
      D rounds threshold N F xi U) width hwidth a b
  have hroot := measurableSet_isViable_canonicalIntervalResamplingTree
    D rounds hwidth threshold N F xi G (3 / 200) p r hpr hrL
  have hlisted : MeasurableSet {U : IntervalResamplingChoices L q rounds |
      ∀ J : LongIntervalIndex L width,
        J.val ∈ balancedIntervalMergeList width hwidth p r →
        Submodule.IsViable (3 / 200 : ℝ) (S J.val.1 J.val.2 U)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) ∧
          U ∈ canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro J
    by_cases hmem : J.val ∈ balancedIntervalMergeList width hwidth p r
    · simp only [hmem, true_implies]
      exact (measurableSet_isViable_canonicalIntervalResamplingTree
        D rounds hwidth threshold N F xi G (3 / 200) J.val.1 J.val.2
        J.property.1 J.property.2.1).inter
          (measurableSet_canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J)
    · simp only [hmem, false_implies]
      exact MeasurableSet.univ
  exact hroot.inter hlisted

end TNLean.MPS.AreaLaw
