/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.IntervalCollectiveTrimming

/-!
# Recorded spanning vectors on an interval

The count and internal-cut ranks refer to the recorded spanning vectors.
They do not assign the same rank bound to an arbitrary vector in their
span. These facts support ALVV, arXiv:1602.08828v2, collective trimming,
lines 646–697, and the degenerate-ground-space construction,
lines 1777–1817.
-/

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
          (Entropy.cutVector (n := fun _ : interval L p r ↦ q)
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
      (Entropy.cutVector (n := fun _ : interval L p r ↦ q)
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
        (Entropy.cutVector (n := fun _ : interval L p r ↦ q)
          (intervalTrimCut L p r j) (b i))) : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hxiSq
        (Nat.cast_nonneg (Matrix.schmidtRank (WithLp.ofLp
          (Entropy.cutVector (n := fun _ : interval L p r ↦ q)
            (intervalTrimCut L p r j) (b i)))))
    _ ≤ count := by exact_mod_cast hrank.trans hcount

end TNLean.MPS.AreaLaw
