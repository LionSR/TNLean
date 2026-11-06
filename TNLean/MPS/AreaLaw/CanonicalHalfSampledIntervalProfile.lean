/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CanonicalHalfSampledIntervalParent
import TNLean.MPS.AreaLaw.IntervalGenerators
import QICLean.Analysis.CanonicalHalfSamplingParentProperties

/-!
# Unconditional recorded-rank bounds for the complete interval parent

Every finite seed sequence reaches the stated stopping threshold. The same
terminal full-family image and trim therefore have bounded dimension and
recorded internal-cut ranks. No target, gap or successful-sampling event
is required. Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and
collective trimming at lines 660–697.

**Local fix (repeated sampling and terminal amplification):** The output
is the literal corrected parent, including its terminal image and trim;
see https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.
-/

open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- For every finite sequence, any count at least N times the stopping
threshold bounds the number of recorded generators and their weighted
internal-cut ranks. The actual parent dimension has the same bound.
Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and 660–697. -/
theorem isIntervalSpanWithRankBound_canonicalHalfSampledIntervalParent
    {L q p r N D threshold rounds count : ℕ} {xi : ℝ} (hxi : 0 < xi)
    (F : Fin N → EuclideanSpace ℂ (interval L p r → Fin q) →L[ℂ]
      EuclideanSpace ℂ (interval L p r → Fin q))
    (hN : N ≤ D ^ 2) (hthreshold : 2 ≤ threshold) (hcount : N * threshold ≤ count)
    (hrounds : Fintype.card (interval L p r → Fin q) ≤ 2 ^ rounds)
    (W : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q)))
    (U : Fin rounds → Matrix.rankUnitaryProduct
      (Fintype.card (interval L p r → Fin q))) :
    IsIntervalSpanWithRankBound L q p r count xi
      (canonicalHalfSampledIntervalParent L q p r D threshold rounds F xi W U) := by
  classical
  let e := (Fintype.equivFin (interval L p r → Fin q)).symm
  let P := ((Matrix.toEuclideanCLM (n := interval L p r → Fin q) (𝕜 := ℂ)).symm
    W.starProjection).reindex e.symm e.symm
  let Q := Entropy.canonicalHalfSampleTrimIterate e (intervalTrimCut L p r) xi
    (r - p - 1) D threshold (Entropy.nativeFamilyMatrix e F) P
    (Entropy.halfSamplingSeedSequence U) rounds
  let WQ := (Matrix.toEuclideanLin Q).range.map
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap
  let image := ⨆ i, WQ.map (F i).toLinearMap
  have hP : P.rank ≤ 2 ^ rounds := P.rank_le_card_width.trans
    (by simpa only [Fintype.card_fin] using hrounds)
  obtain ⟨_hStop, hImage, _hOutput⟩ :=
    Entropy.finrank_canonicalHalfSamplingParent_le_threshold
      (n := fun _ : interval L p r ↦ q) e (intervalTrimCut L p r) xi
      (r - p - 1) D threshold rounds F
      (by simpa only [Fintype.card_fin] using hN) hthreshold P hP
      (Entropy.halfSamplingSeedSequence U)
  have hRange : (Matrix.toEuclideanLin (Matrix.familySupportProj
      (fun i ↦ Entropy.nativeFamilyMatrix e F i * Q))).range = image :=
    Matrix.range_familySupportProj_comp_linearIsometryEquiv
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e) F Q
  have hImageDim : Module.finrank ℂ image ≤ count := by
    apply (show Module.finrank ℂ image ≤ N * threshold from ?_).trans hcount
    rw [← hRange]
    change Module.finrank ℂ ((Matrix.toEuclideanLin (Matrix.familySupportProj
      (fun i ↦ Entropy.nativeFamilyMatrix e F i * Q))).range) ≤
        Fintype.card (Fin N) * threshold at hImage
    simpa only [Fintype.card_fin] using hImage
  have hProfile := isIntervalSpanWithRankBound_intervalTrimSubspace
    hxi (stdOrthonormalBasis ℂ image) hImageDim
  change IsIntervalSpanWithRankBound L q p r count xi
    (Entropy.nativeFamilyTrimSpace e (intervalTrimCut L p r) xi (r - p - 1) F Q)
  exact (Entropy.nativeFamilyTrimSpace_eq_trimSubspace
    (n := fun _ : interval L p r ↦ q) e (intervalTrimCut L p r) xi
    (r - p - 1) F Q).symm ▸ hProfile

end TNLean.MPS.AreaLaw
