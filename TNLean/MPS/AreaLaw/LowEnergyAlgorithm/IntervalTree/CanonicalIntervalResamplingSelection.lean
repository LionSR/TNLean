/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalIntervalRawHistory
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTree.CanonicalIntervalResampling

/-!
# Selecting one certified family on every actual interval

One family is selected on each long interval, preserving any accompanying
mathematical certificate. The existing finite-resampling recursion then supplies
its measurable original-target history event and a single joint failure bound.
The unconditional dimension and internal-cut rank estimates hold on every seed.
A short full root has no internal parent and its success event is the whole
seed space, including an empty whole chain.

This conditional auxiliary supports ALVV, arXiv:1602.08828v2,
lines 749–755 and `t:alg1`, lines 1777–1817. Its fixed-candidate history
estimates remain explicit assumptions; primitive-chain constructions discharge
them separately. No new recursion or sampling event is introduced.

It also contains the following results.

* `TNLean.MPS.AreaLaw.canonicalIntervalResamplingGood`,
  `TNLean.MPS.AreaLaw.measurableSet_canonicalIntervalResamplingGood`: the actual joint success event
  of the repeated-sampling tree.
-/

open ManyBody (interval)
open MeasureTheory

section CanonicalIntervalResamplingGood

/-!
## The actual joint success event of the repeated-sampling tree

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

end CanonicalIntervalResamplingGood

section CanonicalIntervalResamplingSelection

open scoped ENNReal

namespace TNLean.MPS.AreaLaw

/-- Select the interval families once while preserving an arbitrary additional
certificate, then use their actual canonical resampling tree. The same
fixed-candidate estimates yield one root/list history bound, and all seed
sequences satisfy the dimension and recorded-rank profile. Conditional auxiliary
to ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. -/
theorem exists_canonical_interval_resampling_tree_with_certificate
    {L q width D rounds count : ℕ} (hwidth : 1 ≤ width) (hq : 1 ≤ q)
    (threshold : ℕ) (hthreshold : 2 ≤ threshold)
    (hcount : D ^ 2 * threshold ≤ count) (hleaf : q ^ width ≤ count)
    (hrounds : ∀ J : LongIntervalIndex L width,
      Fintype.card (interval L J.val.1 J.val.2 → Fin q) ≤ 2 ^ rounds)
    (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q))) (beta : ℝ≥0∞)
    (Certificate : ∀ (J : LongIntervalIndex L width) (n : ℕ),
      (Fin n → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) → Prop) :
    let Fixed := fun (J : LongIntervalIndex L width) (n : ℕ)
      (F : Fin n → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)) ↦
      ∀ W : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
        Submodule.IsViable 0.04 W
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) →
        Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar
          (Fintype.card (interval L J.val.1 J.val.2 → Fin q)))
          (canonicalHalfSampledIntervalHistory L q J.val.1 J.val.2 D
            threshold rounds F xi W G)ᶜ ≤ beta ∧
        ∀ v ∈ canonicalHalfSampledIntervalHistory L q J.val.1 J.val.2 D
            threshold rounds F xi W G,
          Submodule.IsViable (3 / 200)
            (canonicalHalfSampledIntervalParent L q J.val.1 J.val.2 D
              threshold rounds F xi W v)
            (G.map (Entropy.regionTensorCoordinates q
              (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)
    (∀ J : LongIntervalIndex L width, ∃ n F,
      Certificate J n F ∧ n ≤ D ^ 2 ∧ Fixed J n F) →
    ∃ (N : LongIntervalIndex L width → ℕ)
      (F : ∀ J : LongIntervalIndex L width,
        Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
          EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q)),
      (∀ J, Certificate J (N J) (F J) ∧ N J ≤ D ^ 2 ∧ Fixed J (N J) (F J)) ∧
      let thresholdFamily := fun _ : LongIntervalIndex L width ↦ threshold
      let Good := canonicalIntervalResamplingGood D rounds hwidth thresholdFamily N F xi G 0 L
      MeasurableSet Good ∧
      intervalResamplingMeasure L q rounds Goodᶜ ≤ ((L - 1 : ℕ) : ℝ≥0∞) * beta ∧
      (L ≤ width → Good = Set.univ) ∧
      ∀ (U : IntervalResamplingChoices L q rounds) (p r : ℕ)
        (_hpr : p ≤ r) (_hrL : r ≤ L),
        let S := balancedIntervalSpace (canonicalIntervalResamplingOperation
          D rounds thresholdFamily N F xi U) width hwidth p r
        Module.finrank ℂ S ≤ count ∧
          IsIntervalSpanWithRankBound L q p r count xi S := by
  classical
  intro Fixed hparent
  choose N F hparent using hparent
  refine ⟨N, F, hparent, ?_⟩
  intro thresholdFamily Good
  refine ⟨measurableSet_canonicalIntervalResamplingGood
    D rounds hwidth thresholdFamily N F xi G 0 L (Nat.zero_le L) le_rfl, ?_, ?_, ?_⟩
  · exact intervalResamplingMeasure_canonical_tree_joint_history_failure_le
      D rounds hwidth thresholdFamily N F xi G beta
      (fun J W hW ↦ (hparent J).2.2 W hW) 0 L (Nat.zero_le L) le_rfl
  · intro hshort
    apply Set.eq_univ_iff_forall.mpr
    intro U
    refine ⟨?_, ?_⟩
    · change Submodule.IsViable (3 / 200)
        (balancedIntervalSpace (canonicalIntervalResamplingOperation
          D rounds thresholdFamily N F xi U) width hwidth 0 L)
        (G.map (Entropy.regionTensorCoordinates q (interval L 0 L)).toLinearEquiv.toLinearMap)
      rw [balancedIntervalSpace_of_short _ hwidth (show L - 0 ≤ width from hshort)]
      exact Submodule.isViable_top (3 / 200) (by norm_num) _
    · intro J hJ
      have hempty : balancedIntervalMergeList width hwidth 0 L = [] := by
        rw [balancedIntervalMergeList,
          dite_eq_left (by simpa only [Nat.sub_zero] using hshort)]
      simp only [hempty, List.not_mem_nil] at hJ
  · intro U p r hpr hrL
    exact canonicalIntervalResamplingTree_profile hwidth hq thresholdFamily N F
      (fun J ↦ (hparent J).2.1) (fun _ ↦ hthreshold)
      (fun J ↦ (Nat.mul_le_mul_right threshold (hparent J).2.1).trans hcount)
      hrounds hxi hxi1 hleaf U p r hpr hrL

end TNLean.MPS.AreaLaw

end CanonicalIntervalResamplingSelection
