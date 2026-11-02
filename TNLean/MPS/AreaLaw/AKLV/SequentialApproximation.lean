/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SequentialTruncation
import TNLean.MPS.AreaLaw.MPSApproximation

/-!
# Normalized sequential spectral truncation

Uniform Schmidt-tail bounds give an actual normalized matrix product
approximation by the ordered product of leading regional spectral
projections. The proof uses the general sequential truncation estimate
and the elementary normalization inequality; it invokes no area-law
or matrix product approximation existence theorem.

This is the final assembly in AKLV, arXiv:1301.1162v1, lines 1503--1517,
using the general sequential truncation argument.
-/

open Matrix
open scoped BigOperators InnerProductSpace

namespace TNLean.MPS.AreaLaw

/-- The actual ordered product of leading regional spectral projections. -/
noncomputable def aklvSpectralTruncation {L q : ℕ}
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (D : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) :=
  sequentialTruncation (fun k ↦ (Entropy.regionState_isHermitian
    (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω).leadingEigenprojection D) (L - 1) Ω

/-- The normalization of the actual ordered spectral truncation. -/
noncomputable def aklvNormalizedSpectralTruncation {L q : ℕ}
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (D : ℕ) :
    EuclideanSpace ℂ (Fin L → Fin q) :=
  (‖aklvSpectralTruncation Ω D‖ : ℂ)⁻¹ • aklvSpectralTruncation Ω D

/-- Uniform discarded mass at the internal cuts bounds the error of the
actual normalized ordered spectral truncation. Empty and one-site chains
are included. -/
theorem aklvNormalizedSpectralTruncation_spec {L q D : ℕ}
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (htail : ∀ k ∈ Finset.Ico 1 L,
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) Ω).kyFanNorm D ≤ epsilon ^ 2 / (16 * ((L : ℝ) + 1))) :
    aklvSpectralTruncation Ω D ≠ 0 ∧
      ‖aklvNormalizedSpectralTruncation Ω D‖ = 1 ∧
      IsOpenMPS L q D (fun x ↦ aklvNormalizedSpectralTruncation Ω D x) ∧
      ‖aklvNormalizedSpectralTruncation Ω D - Ω‖ ≤ epsilon := by
  classical
  let Φ0 := aklvSpectralTruncation Ω D
  have hcard : ((Finset.Ico 1 L).card : ℝ) ≤ (L : ℝ) + 1 := by
    rw [Nat.card_Ico]
    exact_mod_cast (by omega : L - 1 ≤ L + 1)
  have hsum : (∑ k ∈ Finset.Ico 1 L,
      (1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) Ω).kyFanNorm D)) ≤ epsilon ^ 2 / 16 := by
    calc
      _ ≤ (Finset.Ico 1 L).card • (epsilon ^ 2 / (16 * ((L : ℝ) + 1))) :=
        Finset.sum_le_card_nsmul _ _ _ htail
      _ ≤ ((L : ℝ) + 1) * (epsilon ^ 2 / (16 * ((L : ℝ) + 1))) := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = epsilon ^ 2 / 16 := by field_simp
  have herr : ‖Φ0 - Ω‖ ^ 2 ≤ epsilon ^ 2 / 16 :=
    (norm_sequentialTruncation_leadingEigenprojection_sub_sq_le Ω hΩ D).trans hsum
  have hdist : ‖Φ0 - Ω‖ ≤ epsilon / 4 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [herr]
  have hpos : 0 < ‖Φ0‖ := by
    have hn := norm_sub_norm_le Ω Φ0
    rw [hΩ, norm_sub_rev] at hn
    linarith
  have hne : Φ0 ≠ 0 := norm_pos_iff.mp hpos
  have hunit : ‖aklvNormalizedSpectralTruncation Ω D‖ = 1 :=
    norm_smul_inv_norm (𝕜 := ℂ) hne
  have hmps := (isOpenMPS_sequentialTruncation_leadingEigenprojection Ω hΩ D).1
  refine ⟨hne, hunit, hmps.smul (‖Φ0‖ : ℂ)⁻¹, ?_⟩
  have hnormalized := norm_inv_norm_smul_sub_le_two_mul hΩ hne
  change ‖aklvNormalizedSpectralTruncation Ω D - Ω‖ ≤ 2 * ‖Φ0 - Ω‖ at hnormalized
  linarith

end TNLean.MPS.AreaLaw
