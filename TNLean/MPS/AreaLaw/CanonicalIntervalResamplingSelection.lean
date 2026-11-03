/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalResamplingGood
import TNLean.MPS.AreaLaw.CanonicalIntervalRawTreeProbability
import TNLean.MPS.AreaLaw.CanonicalIntervalResamplingProfile

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
-/

open MeasureTheory
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
