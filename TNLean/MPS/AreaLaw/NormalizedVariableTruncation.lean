/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SequentialTruncation
import QICLean.Analysis.UnitNormalizationDistance

/-!
# Normalized sequential truncation with distinct cut ranks

Each prefix is projected onto its own number of leading marginal
eigenvectors. The one ordered product retains the requested rank at every
internal cut, and its squared error is controlled by the sum of the actual
discarded masses. Normalizing this product preserves every cut rank.

This is the nonuniform form of the sequential truncation estimate used in
ALVV, arXiv:1602.08828v2, Theorem `thm:al-ld`, lines 1096–1105: one
specified cut may use a sharper accuracy budget than the remaining cuts.
-/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

namespace TNLean.MPS.AreaLaw

/-- Scalar multiplication acts entrywise on each cut matrix. -/
theorem cutMatrix_smul {L q : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q))
    (c : ℂ) (k : ℕ) : cutMatrix (c • ψ) k = c • cutMatrix ψ k := by
  ext a b
  rfl

/-- The actual normalized sequential projection product retains distinct
rank budgets at the different cuts. Its input is the sum of the actual
missing marginal masses. Supporting ALVV, arXiv:1602.08828v2,
Theorem `thm:al-ld`, lines 1096–1105. -/
theorem normalized_sequentialTruncation_of_prefix_mass
    {L q : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
    (D : ℕ → ℕ) (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (htail : (∑ k ∈ Finset.Ico 1 L,
      (1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).kyFanNorm (D k))) ≤ delta / 8) :
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).leadingEigenprojection (D k)
    let Φ0 := sequentialTruncation P (L - 1) ψ
    0 < ‖Φ0‖ ∧
      let Φ := (‖Φ0‖ : ℂ)⁻¹ • Φ0
      ‖Φ‖ = 1 ∧
      (∀ k : ℕ, 0 < k → k < L → (cutMatrix Φ k).rank ≤ D k) ∧
      1 - delta < ‖⟪Φ, ψ⟫_ℂ‖ ∧ ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
  classical
  intro P Φ0
  have hspec (k : ℕ) := (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
    (leftBlock L k) ψ).leadingEigenprojection_spec (D k)
  have hP (k : ℕ) : IsStarProjection (P k) :=
    ⟨(hspec k).2.1, Matrix.isHermitian_iff_isSelfAdjoint.mp (hspec k).1⟩
  have hrank0 := (sequentialTruncation_prefix_rank_error P ψ hP).1
  have hmass (k : ℕ) :
      ‖Matrix.toEuclideanLin (Entropy.localLift (leftBlock L k) (1 - P k)) ψ‖ ^ 2 =
        1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
          (leftBlock L k) ψ).kyFanNorm (D k) := by
    rw [Entropy.norm_sq_toEuclideanLin_localLift_eq_trace (hP k).one_sub]
    refine (hspec k).2.2.2.2.2.trans ?_
    rw [Entropy.trace_regionState_eq_one hψ, Complex.one_re]
  have herr : ‖Φ0 - ψ‖ ^ 2 ≤ delta / 8 := by
    have heq : (∑ i ∈ Finset.range (L - 1),
        ‖Matrix.toEuclideanLin (Entropy.localLift (leftBlock L (L - 1 - i))
          (1 - P (L - 1 - i))) ψ‖ ^ 2) =
        ∑ k ∈ Finset.Ico 1 L, (1 -
          (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
            (leftBlock L k) ψ).kyFanNorm (D k)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      conv_lhs => rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' : i < L - 1 := Finset.mem_range.mp hi
      rw [show L - 1 - (L - 1 - 1 - i) = 1 + i by omega, hmass]
    rw [norm_sub_rev]
    exact (norm_sub_sequentialTruncation_sq_le P hP ψ (L - 1)).trans
      (heq.le.trans htail)
  have hdistlt : ‖Φ0 - ψ‖ < 1 := by nlinarith only [herr, hdelta1, norm_nonneg (Φ0 - ψ)]
  have hpos : 0 < ‖Φ0‖ := by
    have hn := norm_sub_norm_le ψ Φ0
    rw [hψ, norm_sub_rev] at hn
    linarith only [hn, hdistlt]
  refine ⟨hpos, ?_⟩
  intro Φ
  have hΦ : ‖Φ‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) (norm_pos_iff.mp hpos)
  have hdist : ‖Φ - ψ‖ ≤ 2 * ‖Φ0 - ψ‖ :=
    norm_inv_norm_smul_sub_le_two_mul hψ (norm_pos_iff.mp hpos)
  have hsq : ‖Φ - ψ‖ ^ 2 ≤ delta / 2 := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    nlinarith only [hs, herr]
  refine ⟨hΦ, ?_, ?_, hsq⟩
  · intro k hk hkL
    change (cutMatrix ((‖Φ0‖ : ℂ)⁻¹ • Φ0) k).rank ≤ D k
    rw [cutMatrix_smul, Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero
        (inv_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')))]
    exact (hrank0 k (by omega) hkL).trans
      ((hspec k).2.2.2.1.trans_le (min_le_left _ _))
  · have heq := norm_sub_sq (𝕜 := ℂ) Φ ψ
    simp only [hΦ, hψ, one_pow, RCLike.re_to_complex] at heq
    have hre := Complex.re_le_norm (⟪Φ, ψ⟫_ℂ)
    nlinarith only [heq, hre, hsq, hdelta]

end TNLean.MPS.AreaLaw
