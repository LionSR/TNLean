/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalIntervalResampling
import TNLean.MPS.AreaLaw.CanonicalHalfSampledIntervalProfile
import TNLean.MPS.AreaLaw.IntervalFullSpaceProfile

/-!
# Unconditional size profiles of the actual finite-resampling tree

Full leaves and every literal complete parent satisfy the same recorded
count and internal-cut rank bound for all global sequences. The number
of rounds bounds every physical interval dimension before any candidate
or sample is chosen. These are size bounds, without a viability premise.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 1777–1817.

**Local fix (repeated sampling and terminal amplification):** The actual
operation is the corrected parent with its terminal full image and trim;
see https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
-/

namespace TNLean.MPS.AreaLaw

/-- Every actual retained interval space has the same dimension and
recorded-generator rank ceiling on every sequence. No successful sample
or child viability is assumed. Supporting ALVV, arXiv:1602.08828v2,
lines 749–755 and 1777–1817. -/
theorem canonicalIntervalResamplingTree_profile {L q width D rounds count : ℕ}
    (hwidth : 1 ≤ width) (hq : 1 ≤ q)
    (threshold N : LongIntervalIndex L width → ℕ)
    (F : ∀ J : LongIntervalIndex L width,
      Fin (N J) → EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q) →L[ℂ]
        EuclideanSpace ℂ (interval L J.val.1 J.val.2 → Fin q))
    (hN : ∀ J, N J ≤ D ^ 2) (hthreshold : ∀ J, 2 ≤ threshold J)
    (hcount : ∀ J, N J * threshold J ≤ count)
    (hrounds : ∀ J : LongIntervalIndex L width,
      Fintype.card (interval L J.val.1 J.val.2 → Fin q) ≤ 2 ^ rounds)
    {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi ≤ 1) (hleaf : q ^ width ≤ count)
    (U : IntervalResamplingChoices L q rounds)
    (p r : ℕ) (hpr : p ≤ r) (hrL : r ≤ L) :
    let S := balancedIntervalSpace
      (canonicalIntervalResamplingOperation D rounds threshold N F xi U) width hwidth p r
    Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S := by
  let P := fun (p r : ℕ) (S : Submodule ℂ
      (EuclideanSpace ℂ (interval L p r → Fin q))) ↦
    Module.finrank ℂ S ≤ count ∧ IsIntervalSpanWithRankBound L q p r count xi S
  apply balancedIntervalSpace_invariant
    (canonicalIntervalResamplingOperation D rounds threshold N F xi U)
    hwidth P ?_ ?_ p r hpr hrL
  · intro p r _hpr _hrL hshort
    exact interval_top_dimension_and_rank_bounds hq hxi.le hxi1 hleaf hshort
  · intro p k r hpk hkr hrL hlong S1 S2 _hS1 _hS2
    let J : LongIntervalIndex L width := ⟨(p, r), hpk.trans hkr, hrL, hlong⟩
    have hop : canonicalIntervalResamplingOperation D rounds threshold N F xi U
        p k r hpk hkr S1 S2 =
        canonicalHalfSampledIntervalParent L q p r D (threshold J) rounds (F J) xi
          (adjacentIntervalMerge L q p k r hpk hkr S1 S2)
          (U (LongIntervalIndex.coordinate J)) := by
      simp only [canonicalIntervalResamplingOperation, independentIntervalOperation,
        dite_eq_left hrL, dite_eq_left hlong]
      rfl
    rw [hop]
    have h := isIntervalSpanWithRankBound_canonicalHalfSampledIntervalParent
      hxi (F J) (hN J) (hthreshold J) (hcount J) (hrounds J)
      (adjacentIntervalMerge L q p k r hpk hkr S1 S2) (U (LongIntervalIndex.coordinate J))
    exact ⟨h.finrank_le, h⟩

end TNLean.MPS.AreaLaw
