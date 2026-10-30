/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.RegionalNormalization

/-!
# AKLV robustness from the unshifted chain

The regional shifts, their positivity, and the normalized energy range
are derived from the original nearest-neighbour positive contractions.
Only the original ground eigenvector and gap are spectral inputs.
The cutoff uses the universal upper bound six for the shifted energy.

**Local fix:** Normalization uses the corrected middle-core shift described
in `docs/paper-gaps/aklv13_robustness_constants.tex`.

Source: AKLV, arXiv:1301.1162v1, Section 6.1 and Theorem 6.1.
-/

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace TNLean.MPS.AreaLaw.AKLV

/-- The robustness theorem for an original nearest-neighbour chain. The
three normalization shifts are constructed, rather than supplied with
positivity or an energy budget. The actual separately clipped exterior
blocks have gap at least half the original gap and an exponentially
close phase-aligned unit ground vector.
Source: AKLV, arXiv:1301.1162v1, Theorem 6.1 and Section 6.1. -/
theorem original_chain_robustness {L q : ℕ} [NeZero q]
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ => q) (h i)
      (interval L i.val (i.val + 2)))
    (h0 : ∀ i, 0 ≤ h i) (h1 : ∀ i, h i ≤ 1)
    (a b : Fin (L - 1)) (hab : a.val + 2 < b.val)
    (E g t : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (ht : 32768 * (6 + g) / g ^ 2 ≤ t)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (heig : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (∑ i, h i) Ω =
      (E : ℂ) • Ω)
    (hgap : ((∑ i, h i) - (E : ℂ) • 1 - (g : ℂ) •
      (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef) :
    ∃ z : Fin 3 → ℝ,
      let e := E - ∑ j, z j
      let K := twoSidedEnergyTruncation (leftCutBlock h a (z 0))
        (middleCutBlock h a b (z 1) + (h a + h b)) (rightCutBlock h b (z 2)) t
      0 ≤ e ∧ e ≤ 6 ∧
      ∃ (e' : ℝ) (φ : EuclideanSpace ℂ (Fin L → Fin q)),
        ‖φ‖ = 1 ∧ Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) K φ =
          (e' : ℂ) • φ ∧ 0 ≤ e' ∧ e' ≤ e ∧
        (K - (e' : ℂ) • 1 - ((g / 2 : ℝ) : ℂ) •
          (1 - Matrix.vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)))).PosSemidef ∧
        ∃ θ : ℝ, ‖Ω - Complex.exp (θ * Complex.I) • φ‖ ^ 2 ≤ Real.exp (-t / 16) := by
  have hnorm : ∑ x, ‖WithLp.ofLp Ω x‖ ^ 2 ≤ 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hΩ]
    norm_num
  have hP := Matrix.one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one
    (WithLp.ofLp Ω) hnorm
  have hlow : ((∑ i, h i) - (E : ℂ) • 1).PosSemidef := by
    have hh := hgap.add (hP.smul (Complex.zero_le_real.mpr hg.le))
    simpa only [sub_add_cancel] using hh
  have heigRaw : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E : ℂ) • WithLp.ofLp Ω := by
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using
      congrArg WithLp.ofLp heig
  obtain ⟨z, hX, hN, hY, he0, he6⟩ := exists_normalized_chain_data h hs h0 h1 a b hab E
    (WithLp.ofLp Ω) (SpectralFilter.star_dotProduct_self_of_norm_eq_one hΩ) heigRaw hlow
  let e := E - ∑ j, z j
  have hshift : (∑ i, h i) - (((z 0 + z 1 + z 2 : ℝ) : ℂ)) • 1 - (e : ℂ) • 1 =
      (∑ i, h i) - (E : ℂ) • 1 := by
    simp only [e, Fin.sum_univ_three, Complex.ofReal_sub, Complex.ofReal_add, sub_smul,
      add_smul]
    abel
  have heigShift : Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      ((∑ i, h i) - (((z 0 + z 1 + z 2 : ℝ) : ℂ)) • 1) Ω = (e : ℂ) • Ω := by
    apply WithLp.ofLp_injective 2
    simp only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_mulVec,
      smul_mulVec, one_mulVec, heigRaw, e, Fin.sum_univ_three, Complex.ofReal_sub, sub_smul]
  have ht' : 32768 * (e + g) / g ^ 2 ≤ t := by
    refine le_trans ?_ ht
    apply div_le_div_of_nonneg_right _ (sq_nonneg g)
    nlinarith only [he6]
  refine ⟨z, he0, he6, ?_⟩
  exact normalized_chain_robustness h hs h0 h1 a b (by omega) (z 0) (z 1) (z 2) e g t
    hX hN hY Ω hΩ he0 he6 hg hg1 ht' heigShift (by rw [hshift]; exact hgap)

end TNLean.MPS.AreaLaw.AKLV
