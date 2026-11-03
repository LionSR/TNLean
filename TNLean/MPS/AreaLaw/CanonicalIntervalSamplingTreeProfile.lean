/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalSamplingOperation
import TNLean.MPS.AreaLaw.CanonicalSampledIntervalBounds
import TNLean.MPS.AreaLaw.IntervalFullSpaceProfile

/-!
# Recorded size bounds throughout the actual canonical sampled tree

The existing balanced recursion consumes the canonical sampled operation.
Full short leaves and every actual sampled parent satisfy one common
dimension and recorded-rank bound for every global seed, without viability
assumptions. Source: ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1777–1817, and Figure `fig:merge-prime`, lines 1668–1670.

The bounds concern recorded spanning vectors. Joint viability probability,
all-span MPS bounds and runtime are separate conclusions.
-/

namespace TNLean.MPS.AreaLaw

/-- Every actually retained interval space has the common dimension and
recorded-generator rank bounds for every global seed, including histories
where viability fails. The existing balanced recursion is unchanged. -/
theorem canonicalIntervalSamplingTree_profile {L q width D s : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q) (hD : 2 ≤ D) (hs : 1 ≤ s)
    (N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hleaf : q ^ width ≤ D ^ 6 * s ^ 3)
    (U : IntervalSamplingChoices L q) (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := balancedIntervalSpace (canonicalIntervalSamplingOperation D s N F xi U)
      width hwidth p r
    Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
      IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S := by
  let P := fun (p r : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L p r → Fin q))) ↦
    Module.finrank ℂ S ≤ D ^ 6 * s ^ 3 ∧
      IsIntervalSpanWithRankBound L q p r (D ^ 6 * s ^ 3) xi S
  apply balancedIntervalSpace_invariant (canonicalIntervalSamplingOperation D s N F xi U)
    hwidth P ?_ ?_ p r hpr hrL
  · intro p r _hpr _hrL hshort
    exact interval_top_dimension_and_rank_bounds hq hxi.le hxi1 hleaf hshort
  · intro p k r hpk hkr hrL hlong S1 S2 _hS1 _hS2
    let J : LongIntervalIndex L width := ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
    have hop : canonicalIntervalSamplingOperation D s N F xi U p k r hpk hkr S1 S2 =
        canonicalSampledIntervalInterleavedTrim L q p r D s (F J) xi
          (adjacentIntervalMerge L q p k r hpk hkr S1 S2)
          (U (⟨p, Nat.lt_succ_of_le ((hpk.trans hkr).trans hrL)⟩,
            ⟨r, Nat.lt_succ_of_le hrL⟩)) := by
      dsimp only [canonicalIntervalSamplingOperation]
      rw [dite_eq_left hrL, dite_eq_left hlong]
    rw [hop]
    exact canonicalSampledIntervalInterleavedTrim_profile hD hs (hN J) (F J) hxi _ _

end TNLean.MPS.AreaLaw
