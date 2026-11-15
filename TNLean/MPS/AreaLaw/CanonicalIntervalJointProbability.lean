/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalGuardedProbability
import TNLean.MPS.AreaLaw.BalancedIntervalFailureProbability
import TNLean.MPS.AreaLaw.BalancedIntervalJointFailure
import QICLean.Analysis.ViableSubspaceBootstrap

/-!
# Joint probability from actual fixed-child parent estimates

An estimate for every valid long parent and every fixed baseline seed
implies simultaneous viability at the root and all its actual internal
descendants. The recursion, its sampling law and all its improving
families are the existing ones. Guarded-event measurability and fresh
coordinate sections are derived, rather than assumed.

This is a conditional analytic auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817. The true fixed-child parent failure
estimate remains an explicit premise; the theorem does not assert that
estimate for arbitrary operator families.
-/

open MeasureTheory
open scoped ENNReal

namespace TNLean.MPS.AreaLaw

/-- Fixed-child bounds for the literal canonical parents imply a joint
failure bound for one actual root hierarchy. Only nonnegative viability
error and the fixed-child analytic estimates are required; short leaves,
listed Borel events and true coordinate sections are derived. Conditional
auxiliary to ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem intervalSamplingMeasure_canonical_tree_joint_failure_le
    {L q width : ℕ} (D s : ℕ) (hwidth : 1 ≤ width)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (hdelta : 0 ≤ delta) (beta : ℝ≥0∞)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let operation := canonicalIntervalSamplingOperation D s N F xi
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    (∀ (a b : ℕ) (hab : a ≤ b) (hbL : b ≤ L) (hlong : width < b - a)
      (U : IntervalSamplingChoices L q),
      let k := a + (b - a) / 2
      let hak : a ≤ k := by dsimp only [k]; omega
      let hkb : k ≤ b := by dsimp only [k]; omega
      let J : LongIntervalIndex L width := ⟨(a, b), hab, hbL, hlong⟩
      let left := balancedIntervalSpace (operation U) width hwidth a k
      let right := balancedIntervalSpace (operation U) width hwidth k b
      P a k left → P k b right →
        Matrix.rankUnitaryHaar (Fintype.card (interval L a b → Fin q))
          {v | ¬P a b (canonicalSampledIntervalInterleavedTrim L q a b D s (F J) xi
            (adjacentIntervalMerge L q a k b hak hkb left right) v)} ≤ beta) →
    intervalSamplingMeasure L q
      {U | ¬(P p r (balancedIntervalSpace (operation U) width hwidth p r) ∧
        ∀ J ∈ balancedIntervalMergeList width hwidth p r,
          P J.1 J.2 (balancedIntervalSpace (operation U) width hwidth J.1 J.2))} ≤
      ((r - p - 1 : ℕ) : ℝ≥0∞) * beta := by
  unfold canonicalIntervalSamplingOperation intervalSamplingMeasure
  exact pi_independentIntervalTree_joint_failure_le
    (Ω := fun J ↦ Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s
      (F J) xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim
      D s (F J) xi W hW) hwidth
    (fun J ↦ Matrix.rankUnitaryHaar
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    G delta hdelta beta p r hpr hrL

end TNLean.MPS.AreaLaw
