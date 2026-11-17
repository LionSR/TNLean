/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalRawHistory
import TNLean.MPS.AreaLaw.BalancedIntervalHistoryProbability

/-!
# Joint original-target histories of the actual repeated-sampling tree

The fixed-candidate estimate for the literal stopped history yields one
joint bound for retained viability and every listed parent's same history.
The history is the existing original-target event, not an intersection of
all soft spectral targets. This conditional analytic composition supports
ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817. The fixed-candidate
probability and history-to-parent implication remain explicit premises.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

namespace TNLean.MPS.AreaLaw

/-- True fixed-candidate estimates for the literal original-target history
control retained viability and the same history at every listed parent
with one merge count. All Borel and actual-coordinate section properties
are derived. Conditional auxiliary to ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
theorem intervalResamplingMeasure_canonical_tree_joint_history_failure_le
    {L q width : ℕ} (D rounds : ℕ) (hwidth : 1 ≤ width)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (beta : ℝ≥0∞)
    (hfixed : ∀ (J : LongIntervalIndex L width)
      (W : Submodule ℂ (EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))),
      Submodule.IsViable 0.04 W
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) →
      Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar
          (Fintype.card (interval L J.val.1 J.val.2 → Fin q)))
        (canonicalHalfSampledIntervalHistory L q J.val.1 J.val.2 D
          (threshold J) rounds (F J) xi W G)ᶜ ≤ beta ∧
      ∀ v ∈ canonicalHalfSampledIntervalHistory L q J.val.1 J.val.2 D
        (threshold J) rounds (F J) xi W G,
        Submodule.IsViable (3 / 200)
          (canonicalHalfSampledIntervalParent L q J.val.1 J.val.2 D
            (threshold J) rounds (F J) xi W v)
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap))
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := fun (a b : ℕ) (U : IntervalResamplingChoices L q rounds) ↦
      balancedIntervalSpace (canonicalIntervalResamplingOperation
        D rounds threshold N F xi U) width hwidth a b
    let P := fun (a b : ℕ) (W : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable (3 / 200) W
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    intervalResamplingMeasure L q rounds
      {U | ¬(P p r (S p r U) ∧
        ∀ J : LongIntervalIndex L width,
          J.val ∈ balancedIntervalMergeList width hwidth p r →
          P J.val.1 J.val.2 (S J.val.1 J.val.2 U) ∧
            U ∈ canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J)} ≤
      ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  classical
  intro S P
  let H := fun J : ℕ × ℕ ↦ if h : J.1 ≤ J.2 ∧ J.2 ≤ L ∧ width < J.2 - J.1 then
    canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G ⟨J, h⟩ else ∅
  let operation := canonicalIntervalResamplingOperation D rounds threshold N F xi
  let μ := fun J : Fin (L + 1) × Fin (L + 1) ↦
    Measure.pi (fun _ : Fin rounds ↦ Matrix.rankUnitaryHaar
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
  let E := fun J : ℕ × ℕ ↦
    {U : IntervalResamplingChoices L q rounds | let k := J.1 + (J.2 - J.1) / 2
      P J.1 k (S J.1 k U) ∧ P k J.2 (S k J.2 U) ∧ U ∉ H J}
  have hleaf (a b : ℕ) (_hab : a ≤ b) (_hbL : b ≤ L) (_hshort : b - a ≤ width) :
      P a b ⊤ := Submodule.isViable_top (3 / 200) (by norm_num) _
  have hnode (J : ℕ × ℕ) (hJ : J ∈ balancedIntervalMergeList width hwidth p r)
      (U : IntervalResamplingChoices L q rounds) :
      let k := J.1 + (J.2 - J.1) / 2
      P J.1 k (S J.1 k U) → P k J.2 (S k J.2 U) →
      U ∈ H J → P J.1 J.2 (S J.1 J.2 U) := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr hJ
    let I : LongIntervalIndex L width := ⟨J, hb.2.1, hb.2.2.1.trans hrL, hb.2.2.2⟩
    intro k hleft hright hhistory
    have hak : J.1 ≤ k := by dsimp only [k]; omega
    have hkb : k ≤ J.2 := by dsimp only [k]; omega
    let W := adjacentIntervalMerge L q J.1 k J.2 hak hkb (S J.1 k U) (S k J.2 U)
    have hW : Submodule.IsViable 0.04 W
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.1 J.2)).toLinearEquiv.toLinearMap) :=
      Submodule.IsCloseTo.of_le (isViable_adjacentIntervalMerge hak hkb G _ _ hleft hright)
        (by norm_num)
    have hvalid : J.1 ≤ J.2 ∧ J.2 ≤ L ∧ width < J.2 - J.1 := I.property
    have hhistory' : U ∈
        canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G I := by
      simpa only [H, dite_eq_left hvalid] using hhistory
    have hlocal := (hfixed I W hW).2 (U (LongIntervalIndex.coordinate I)) hhistory'
    have hvalue : S J.1 J.2 U = canonicalHalfSampledIntervalParent
        L q J.1 J.2 D (threshold I) rounds (F I) xi W
          (U (LongIntervalIndex.coordinate I)) := by
      change balancedIntervalSpace (operation U) width hwidth J.1 J.2 = _
      rw [balancedIntervalSpace, dite_eq_right (by omega : ¬J.2 - J.1 ≤ width)]
      simp only [operation, canonicalIntervalResamplingOperation,
        independentIntervalOperation, dite_eq_left (hb.2.2.1.trans hrL), dite_eq_left hb.2.2.2]
      rfl
    exact hvalue.symm ▸ hlocal
  have hE (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r}) :
      MeasurableSet (E J.val) := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
    let I : LongIntervalIndex L width :=
      ⟨J.val, hb.2.1, hb.2.2.1.trans hrL, hb.2.2.2⟩
    let k := J.val.1 + (J.val.2 - J.val.1) / 2
    have hak : J.val.1 ≤ k := by dsimp only [k]; omega
    have hkb : k ≤ J.val.2 := by dsimp only [k]; omega
    have hleft := measurableSet_isViable_canonicalIntervalResamplingTree
      D rounds hwidth threshold N F xi G (3 / 200) J.val.1 k
      hak (hkb.trans I.property.2.1)
    have hright := measurableSet_isViable_canonicalIntervalResamplingTree
      D rounds hwidth threshold N F xi G (3 / 200) k J.val.2 hkb I.property.2.1
    have hhistory := measurableSet_canonicalIntervalResamplingHistory
      D rounds hwidth threshold N F xi G I
    have hvalid : J.val.1 ≤ J.val.2 ∧ J.val.2 ≤ L ∧ width < J.val.2 - J.val.1 := I.property
    have hH : H J.val =
        canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G I := by
      dsimp only [H]
      rw [dite_eq_left hvalid]
    change MeasurableSet {U | P J.val.1 k (S J.val.1 k U) ∧
      P k J.val.2 (S k J.val.2 U) ∧ U ∉ H J.val}
    rw [hH]
    exact hleft.inter (hright.inter hhistory.compl)
  have hsection (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r})
      (U : IntervalResamplingChoices L q rounds) :
      μ (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J)
        {v | Function.update U (balancedIntervalMergeCoordinate width hwidth p r hpr hrL J) v
          ∈ E J.val} ≤ beta := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
    let I : LongIntervalIndex L width :=
      ⟨J.val, hb.2.1, hb.2.2.1.trans hrL, hb.2.2.2⟩
    let coord := LongIntervalIndex.coordinate I
    let k := J.val.1 + (J.val.2 - J.val.1) / 2
    have hak : J.val.1 ≤ k := by dsimp only [k]; omega
    have hkb : k ≤ J.val.2 := by dsimp only [k]; omega
    change μ coord {v | Function.update U coord v ∈ E J.val} ≤ beta
    have hshorter (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L)
        (hlen : b - a < J.val.2 - J.val.1)
        (v : Fin rounds → Matrix.rankUnitaryProduct
          (Fintype.card (interval L J.val.1 J.val.2 → Fin q))) :
        S a b (Function.update U coord v) = S a b U := by
      apply (measurable_projectionMatrix_and_dependsOn_canonicalIntervalResamplingTree
        D rounds hwidth threshold N F xi a b hab hbL).2
      intro B hB
      have hne : B ≠ coord := by
        intro heq
        subst B
        change J.val.2 - J.val.1 ≤ b - a at hB
        omega
      exact Function.update_of_ne hne v U
    have hleft (v) := hshorter J.val.1 k hak (hkb.trans I.property.2.1)
      (by dsimp only [k]; omega) v
    have hright (v) := hshorter k J.val.2 hkb I.property.2.1
      (by dsimp only [k]; omega) v
    by_cases hchildren : P J.val.1 k (S J.val.1 k U) ∧ P k J.val.2 (S k J.val.2 U)
    · let W := adjacentIntervalMerge L q J.val.1 k J.val.2 hak hkb
        (S J.val.1 k U) (S k J.val.2 U)
      have hW : Submodule.IsViable 0.04 W
          (G.map (Entropy.regionTensorCoordinates q
            (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap) :=
        Submodule.IsCloseTo.of_le
          (isViable_adjacentIntervalMerge hak hkb G _ _ hchildren.1 hchildren.2) (by norm_num)
      have hvalid : J.val.1 ≤ J.val.2 ∧ J.val.2 ≤ L ∧ width < J.val.2 - J.val.1 := I.property
      have hH : H J.val =
          canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G I := by
        dsimp only [H]
        rw [dite_eq_left hvalid]
      apply (measure_mono ?_).trans (hfixed I W hW).1
      intro v hv
      change P J.val.1 k (S J.val.1 k (Function.update U coord v)) ∧
        P k J.val.2 (S k J.val.2 (Function.update U coord v)) ∧
        Function.update U coord v ∉ H J.val at hv
      intro hgood
      apply hv.2.2
      rw [hH]
      exact (canonicalIntervalResamplingHistory_update_parent
        D rounds hwidth threshold N F xi G I U v).2 hgood
    · have hempty : {v | Function.update U coord v ∈ E J.val} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro v hv
        apply hchildren
        change P J.val.1 k (S J.val.1 k (Function.update U coord v)) ∧
          P k J.val.2 (S k J.val.2 (Function.update U coord v)) ∧
          Function.update U coord v ∉ H J.val at hv
        exact ⟨(hleft v) ▸ hv.1, (hright v) ▸ hv.2.1⟩
      rw [hempty, measure_empty]
      exact bot_le
  have hbound := pi_balancedIntervalSpace_joint_history_failure_le μ operation
    width hwidth P H hleaf p r hpr hrL
    (balancedIntervalMergeCoordinate width hwidth p r hpr hrL) beta hnode hE hsection
  apply (measure_mono ?_).trans hbound
  intro U hfailure hgood
  apply hfailure
  refine ⟨hgood.1, ?_⟩
  intro J hJ
  have hlisted := hgood.2 J.val hJ
  refine ⟨hlisted.1, ?_⟩
  have hH : H J.val =
      canonicalIntervalResamplingHistory D rounds hwidth threshold N F xi G J := by
    dsimp only [H]
    rw [dite_eq_left J.property]
  rw [← hH]
  exact hlisted.2

end TNLean.MPS.AreaLaw
