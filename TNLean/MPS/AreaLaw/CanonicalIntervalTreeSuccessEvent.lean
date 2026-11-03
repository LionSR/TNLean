/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalSamplingTree
import TNLean.MPS.AreaLaw.BalancedIntervalMergeBounds

/-!
# The true joint success event of one actual sampled hierarchy

The event records viability at the root and every internal interval of
its actual midpoint recursion. It imposes no condition on unrelated
or overlapping intervals. Its measurability follows from that of each
literal retained space. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1777–1817.
-/

open MeasureTheory

namespace TNLean.MPS.AreaLaw

/-- True viability at the specified root and its actual internal
intervals. The sampled spaces and target are the existing ones.
Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
def canonicalIntervalSamplingTreeGood {L q width : ℕ} (D s : ℕ) (hwidth : 1 ≤ width)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) : Set (IntervalSamplingChoices L q) :=
  {U | Submodule.IsViable delta
      (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
        width hwidth p r)
      (G.map (Entropy.regionTensorCoordinates q (interval L p r)).toLinearEquiv.toLinearMap) ∧
    ∀ J ∈ balancedIntervalMergeList width hwidth p r,
      Submodule.IsViable delta
        (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
          width hwidth J.1 J.2)
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.1 J.2)).toLinearEquiv.toLinearMap)}

/-- The actual joint event is Borel; no measurability premise is placed
on the desired success condition. Supporting ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, lines 1777–1817. -/
theorem measurableSet_canonicalIntervalSamplingTreeGood {L q width : ℕ}
    (D s : ℕ) (hwidth : 1 ≤ width) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    MeasurableSet (canonicalIntervalSamplingTreeGood D s hwidth N F xi G delta p r) := by
  have hroot := measurableSet_isViable_canonicalIntervalSamplingTree
    D s hwidth N F xi G delta p r hpr hrL
  have hnodes (J : {J : ℕ × ℕ // J ∈ balancedIntervalMergeList width hwidth p r}) :
      MeasurableSet {U : IntervalSamplingChoices L q | Submodule.IsViable delta
        (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
          width hwidth J.val.1 J.val.2)
        (G.map (Entropy.regionTensorCoordinates q
          (interval L J.val.1 J.val.2)).toLinearEquiv.toLinearMap)} := by
    have hb := bounds_of_mem_balancedIntervalMergeList width hwidth p r hpr J.property
    exact measurableSet_isViable_canonicalIntervalSamplingTree
      D s hwidth N F xi G delta J.val.1 J.val.2 hb.2.1 (hb.2.2.1.trans hrL)
  convert hroot.inter (MeasurableSet.iInter hnodes) using 1
  ext U
  simp only [canonicalIntervalSamplingTreeGood, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_iInter, Subtype.forall]

end TNLean.MPS.AreaLaw
