/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalSamplingTree
import TNLean.MPS.AreaLaw.IndependentIntervalSections

/-!
# Sections of the actual sampled interval recursion

Replacing a long parent's sampling coordinate leaves both shorter child
spaces unchanged. The resulting parent is the actual canonical sampled
merge of those fixed children. This identifies the local sections used
in the ALVV probability estimate, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817.
-/

namespace TNLean.MPS.AreaLaw

/-- The true parent section uses exactly the same two child spaces and
its fresh sampling coordinate. No independent comparison tree is used.
Supporting ALVV, arXiv:1602.08828v2, lines 1777–1817. -/
theorem canonicalIntervalSamplingTree_update_parent {L q width : ℕ}
    (D s : ℕ) (hwidth : 1 ≤ width) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) (hlong : width < r - p) :
    let k := p + (r - p) / 2
    let hpk : p ≤ k := by dsimp only [k]; omega
    let hkr : k ≤ r := by dsimp only [k]; omega
    let J : LongIntervalIndex L width := ⟨(p, r), hpr, hrL, hlong⟩
    let coord : Fin (L + 1) × Fin (L + 1) :=
      (⟨p, Nat.lt_succ_of_le (hpr.trans hrL)⟩, ⟨r, Nat.lt_succ_of_le hrL⟩)
    ∀ (U : IntervalSamplingChoices L q)
      (v : Matrix.rankUnitaryProduct (Fintype.card (interval L p r → Fin q))),
      balancedIntervalSpace
        (canonicalIntervalSamplingOperation D s N F xi (Function.update U coord v))
        width hwidth p r =
      canonicalSampledIntervalInterleavedTrim L q p r D s (F J) xi
        (adjacentIntervalMerge L q p k r hpk hkr
          (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
            width hwidth p k)
          (balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
            width hwidth k r)) v := by
  unfold canonicalIntervalSamplingOperation
  exact independentIntervalTree_update_parent
    (Ω := fun J ↦ Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s
      (F J) xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim
      D s (F J) xi W hW) hwidth p r hpr hrL hlong

/-- The actual guarded failure event is Borel for the specified global
target and its entire regional exterior. Supporting ALVV,
arXiv:1602.08828v2, lines 1777–1817. -/
theorem measurableSet_guardedIntervalFailure_canonicalSamplingTree {L q width : ℕ}
    (D s : ℕ) (hwidth : 1 ≤ width) (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (xi : ℝ) (G : Submodule ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (delta : ℝ) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let P := fun (a b : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L a b → Fin q))) ↦
      Submodule.IsViable delta S
        (G.map (Entropy.regionTensorCoordinates q (interval L a b)).toLinearEquiv.toLinearMap)
    MeasurableSet (guardedIntervalFailure
      (canonicalIntervalSamplingOperation D s N F xi) width hwidth P (p, r)) := by
  unfold canonicalIntervalSamplingOperation
  exact measurableSet_guardedIntervalFailure_independentIntervalTree
    (Ω := fun J ↦ Matrix.rankUnitaryProduct
      (Fintype.card (interval L J.1.val J.2.val → Fin q)))
    (fun J W v ↦ canonicalSampledIntervalInterleavedTrim L q J.val.1 J.val.2 D s
      (F J) xi W v)
    (fun J W hW ↦ measurable_projectionMatrix_canonicalSampledIntervalInterleavedTrim
      D s (F J) xi W hW) hwidth G delta p r hpr hrL

end TNLean.MPS.AreaLaw
