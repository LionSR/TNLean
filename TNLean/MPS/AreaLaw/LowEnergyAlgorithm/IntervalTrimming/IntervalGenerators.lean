/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LowEnergyAlgorithm.IntervalTrimming.IntervalCollectiveTrimming
import QICLean.ManyBody.Subspace.Sampling.CanonicalHalfSamplingParentProperties

/-!
# Recorded spanning vectors on an interval

The count and internal-cut ranks refer to the recorded spanning vectors.
They do not assign the same rank bound to an arbitrary vector in their
span. These facts support ALVV, arXiv:1602.08828v2, collective trimming,
lines 646–697, and the degenerate-ground-space construction,
lines 1777–1817.

## Unconditional recorded-rank bounds for the complete interval parent

Every finite seed sequence reaches the stated stopping threshold. The same
terminal full-family image and trim therefore have bounded dimension and
recorded internal-cut ranks. No target, gap or successful-sampling event
is required. Supporting ALVV, arXiv:1602.08828v2, lines 749–755 and
collective trimming at lines 660–697.

**Local fix (repeated sampling and terminal amplification):** The output
is the literal corrected parent, including its terminal image and trim;
see https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf.

## Dimension and recorded-rank bounds for full short intervals

A full short interval has its original orthonormal basis as a recorded
spanning family. This common leaf argument is shared by the viable-tree
constructions. Source: ALVV, arXiv:1602.08828v2, initialization,
lines 1650–1662. No viability premise is required for these size bounds.
-/

section

open ManyBody (interval)

namespace TNLean.MPS.AreaLaw

/-- A space has at most `count` recorded generators whose internal-cut
Schmidt ranks, multiplied by `xi²`, are at most `count`. Supporting ALVV,
arXiv:1602.08828v2, collective trimming, lines 660–697. This is a property
of a spanning family, not a uniform rank bound on its entire span. -/
def IsIntervalSpanWithRankBound (L q p r count : ℕ) (xi : ℝ)
    (S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) : Prop :=
  ∃ n : ℕ, n ≤ count ∧
    ∃ u : Fin n → EuclideanSpace ℂ (interval L p r → Fin q),
      S = Submodule.span ℂ (Set.range u) ∧
      ∀ j : ℕ, j < r - p - 1 → ∀ i : Fin n,
        xi ^ 2 * Matrix.schmidtRank (WithLp.ofLp
          (ManyBody.cutVector (X := fun _ ↦ Fin q)
            (intervalTrimCut L p r j) (u i))) ≤ count

/-- The recorded generator count bounds the actual subspace dimension.
Supporting ALVV, arXiv:1602.08828v2, collective trimming, lines 662–663. -/
theorem IsIntervalSpanWithRankBound.finrank_le {L q p r count : ℕ} {xi : ℝ}
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))}
    (hS : IsIntervalSpanWithRankBound L q p r count xi S) :
    Module.finrank ℂ S ≤ count := by
  obtain ⟨n, hn, u, hu, _⟩ := hS
  rw [hu]
  apply le_trans ?_ hn
  convert _root_.finrank_range_le_card (R := ℂ) u using 1
  · rfl
  · exact (Fintype.card_fin n).symm

/-- The actual collective trim retains its explicit spanning vectors,
count and rank bounds. Supporting ALVV, arXiv:1602.08828v2,
`lem:trimming`, lines 660–697. -/
theorem isIntervalSpanWithRankBound_intervalTrimSubspace {L q p r n count : ℕ}
    {xi : ℝ} (hxi : 0 < xi)
    {S : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))}
    (u : OrthonormalBasis (Fin n) ℂ S) (hn : n ≤ count) :
    IsIntervalSpanWithRankBound L q p r count xi
      (intervalTrimSubspace L q p r xi (fun i ↦ (u i : _))) := by
  refine ⟨n, hn, intervalTrimVector L q p r xi (fun i ↦ (u i : _)), rfl, ?_⟩
  intro j hj i
  exact (schmidtRank_cutVector_intervalTrimVector_le hxi u hj i).trans (by exact_mod_cast hn)

/-- A full local space has bounded recorded generators whenever its
dimension fits the count budget and the trimming radius is at most one.
Supporting ALVV, arXiv:1602.08828v2, full local initialization,
lines 1650–1662. -/
theorem isIntervalSpanWithRankBound_top {L q p r count : ℕ} {xi : ℝ}
    (hq : 1 ≤ q) (hcount : Module.finrank ℂ
      (EuclideanSpace ℂ (interval L p r → Fin q)) ≤ count)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    IsIntervalSpanWithRankBound L q p r count xi ⊤ := by
  classical
  let b := stdOrthonormalBasis ℂ (EuclideanSpace ℂ (interval L p r → Fin q))
  refine ⟨Module.finrank ℂ (EuclideanSpace ℂ (interval L p r → Fin q)),
    hcount, fun i ↦ b i, b.toBasis.span_eq.symm, ?_⟩
  intro j _hj i
  have hrank : Matrix.schmidtRank (WithLp.ofLp
      (ManyBody.cutVector (X := fun _ ↦ Fin q)
        (intervalTrimCut L p r j) (b i))) ≤
      Module.finrank ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) := by
    calc
      _ ≤ Fintype.card (intervalTrimCut L p r j → Fin q) :=
        Matrix.schmidtRank_le_left _
      _ = q ^ (intervalTrimCut L p r j).card := by simp
      _ ≤ q ^ (interval L p r).card := by
        apply Nat.pow_le_pow_right hq
        simpa only [Fintype.card_coe] using Finset.card_le_univ (intervalTrimCut L p r j)
      _ = Module.finrank ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) := by
        rw [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hxiSq : xi ^ 2 ≤ 1 := pow_le_one₀ hxi0 hxi1
  calc
    _ ≤ (Matrix.schmidtRank (WithLp.ofLp
        (ManyBody.cutVector (X := fun _ ↦ Fin q)
          (intervalTrimCut L p r j) (b i))) : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hxiSq
        (Nat.cast_nonneg (Matrix.schmidtRank (WithLp.ofLp
          (ManyBody.cutVector (X := fun _ ↦ Fin q)
            (intervalTrimCut L p r j) (b i)))))
    _ ≤ count := by exact_mod_cast hrank.trans hcount

end TNLean.MPS.AreaLaw

end

section

open ManyBody (interval)

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

end

section

open ManyBody (card_interval_le interval)

namespace TNLean.MPS.AreaLaw

/-- The full short interval satisfies the common dimension and recorded
rank bounds whenever its full dimension fits the leaf count. -/
theorem interval_top_dimension_and_rank_bounds
    {L q p r width count : ℕ} {xi : ℝ}
    (hq : 1 ≤ q) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hleaf : q ^ width ≤ count) (hshort : r - p ≤ width) :
    Module.finrank ℂ (⊤ : Submodule ℂ (EuclideanSpace ℂ (interval L p r → Fin q))) ≤ count ∧
      IsIntervalSpanWithRankBound L q p r count xi ⊤ := by
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (interval L p r → Fin q)) ≤ count := by
    calc
      _ = q ^ (interval L p r).card := by
        rw [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      _ ≤ q ^ width := Nat.pow_le_pow_right hq ((card_interval_le _ _).trans hshort)
      _ ≤ count := hleaf
  exact ⟨by simpa only [finrank_top] using hdim,
    isIntervalSpanWithRankBound_top hq hdim hxi0 hxi1⟩

end TNLean.MPS.AreaLaw

end
