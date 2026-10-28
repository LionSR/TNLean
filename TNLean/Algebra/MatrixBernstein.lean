/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianMatrixBernstein
import TNLean.Algebra.HermitianDilationIntegral
import Mathlib.Probability.IdentDistrib

/-!
# Matrix Bernstein for independent identically distributed complex matrices

For iid square complex random matrices with common mean `μ` and almost-sure
deviation bound `R`, the sample mean satisfies the Bernstein inequality with
dimension factor `2d`, coefficient `1/3`, and the maximum of the two actual
centered Gram variance norms. The sample count is positive, as required for the
source's arithmetic mean. Matrices carry the Borel sigma algebra of their
finite-dimensional norm topology.

The proof derives measurability from identical distribution, derives all
integrability from the deviation bound, centers the actual samples, and applies
the real-linear Hermitian dilation. Identical distribution identifies both
actual Gram expectations. The one-sided Hermitian bound and the positive
spectral endpoint of the dilation yield the factor `2d` directly.

This proves LVV, arXiv:1307.5143v1, Theorem 2.13, equation (7), the iid complex
square-matrix case quoted from Tropp, *User-friendly tail bounds for sums of random
matrices*, Theorem 1.6:
https://arxiv.org/abs/1307.5143v1 and
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
The variance is the scalar maximum of operator norms, as in Tropp; the notation
in LVV is clarified in `docs/paper-gaps/finite_uniform_matrix_bernstein.tex`.
The sampled-filter construction and its word-frequency bound are separate results.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open MeasureTheory

namespace Matrix

noncomputable local instance {n : Type*} [Fintype n] [DecidableEq n] :
    MeasurableSpace (Matrix n n ℂ) := borel (Matrix n n ℂ)
local instance {n : Type*} [Fintype n] [DecidableEq n] :
    BorelSpace (Matrix n n ℂ) := ⟨rfl⟩

/-- The iid complex matrix Bernstein inequality of LVV, Theorem 2.13,
equation (7), quoted from Tropp, Theorem 1.6. The actual centered Gram expectations
define the variance; no concentration, variance cap or integral identity is assumed. -/
theorem probability_matrix_bernstein
    {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] [Nonempty n]
    {P : Measure Ω} [IsProbabilityMeasure P] (ℓ : ℕ) (hℓ : 0 < ℓ)
    (X : Fin ℓ → Ω → Matrix n n ℂ) (μ : Matrix n n ℂ)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ j, ProbabilityTheory.IdentDistrib (X j) (X ⟨0, hℓ⟩) P P)
    (hmean : ∀ j, ∫ ω, X j ω ∂P = μ) {R t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ j, ∀ᵐ ω ∂P, ‖X j ω - μ‖ ≤ R) :
    let Y := fun j ω ↦ X j ω - μ
    let σ2 := max ‖∫ ω, Y ⟨0, hℓ⟩ ω * (Y ⟨0, hℓ⟩ ω)ᴴ ∂P‖
      ‖∫ ω, (Y ⟨0, hℓ⟩ ω)ᴴ * Y ⟨0, hℓ⟩ ω ∂P‖
    P.real {ω | t ≤ ‖(ℓ : ℝ)⁻¹ • ∑ j, X j ω - μ‖} ≤
      2 * (Fintype.card n : ℝ) * Real.exp (-((ℓ : ℝ) * t ^ 2) / (2 * σ2 + 2 * R * t / 3)) := by
  intro Y σ2
  let D (j : Fin ℓ) (ω : Ω) := hermitianDilation (Y j ω)
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hXm (j : Fin ℓ) : AEMeasurable (X j) P := (hIdent j).aemeasurable_fst
  have hYm (j : Fin ℓ) : AEMeasurable (Y j) P := (hXm j).sub aemeasurable_const
  have hYbound (j : Fin ℓ) : ∀ᵐ ω ∂P, ‖Y j ω‖ ≤ R := hbound j
  have hR : 0 ≤ R := by
    obtain ⟨ω, hω⟩ := (hYbound ⟨0, hℓ⟩).exists
    exact (norm_nonneg _).trans hω
  have hσ : 0 ≤ σ2 := (norm_nonneg _).trans (le_max_left _ _)
  have hYIndep := hIndep.comp (fun _ A ↦ A - μ)
    (fun _ ↦ (continuous_id.sub continuous_const).measurable)
  have hYIdent (j : Fin ℓ) : ProbabilityTheory.IdentDistrib (Y j) (Y ⟨0, hℓ⟩) P P :=
    (hIdent j).comp (continuous_id.sub continuous_const).measurable
  have hYmean (j : Fin ℓ) : ∫ ω, Y j ω ∂P = 0 := by
    have hiY : Integrable (Y j) P := Integrable.of_bound (hYm j).aestronglyMeasurable R (hYbound j)
    have hiX : Integrable (X j) P := by
      have hh := hiY.add (integrable_const μ)
      convert hh using 1
      funext ω
      simp only [Pi.add_apply, Y, sub_add_cancel]
    simp only [Y, integral_sub hiX (integrable_const μ), hmean j, integral_const,
      probReal_univ, one_smul, sub_self]
  have hDm (j : Fin ℓ) : AEMeasurable (D j) P :=
    hermitianDilationLinearIsometry.continuous.measurable.aemeasurable.comp_aemeasurable (hYm j)
  have hDIndep := hYIndep.comp (fun _ A ↦ hermitianDilation A)
    (fun _ ↦ hermitianDilationLinearIsometry.continuous.measurable)
  have hDherm (j : Fin ℓ) : ∀ᵐ ω ∂P, (D j ω).IsHermitian :=
    Filter.Eventually.of_forall fun ω ↦ isHermitian_hermitianDilation _
  have hDmean (j : Fin ℓ) : ∫ ω, D j ω ∂P = 0 := by
    rw [show (fun ω ↦ D j ω) = (fun ω ↦ hermitianDilation (Y j ω)) from rfl,
      integral_hermitianDilation, hYmean j]
    simp only [hermitianDilation, conjTranspose_zero, fromBlocks_zero]
  have hDbound (j : Fin ℓ) : ∀ᵐ ω ∂P, ‖D j ω‖ ≤ R := by
    simpa only [D, norm_hermitianDilation] using hYbound j
  have hDvariance (j : Fin ℓ) : ‖∫ ω, D j ω ^ 2 ∂P‖ ≤ σ2 := by
    have hh := norm_integral_hermitianDilation_sq_le (hYm j).aestronglyMeasurable (hYbound j)
    have hA := ((hYIdent j).comp
      (by fun_prop : Measurable (fun A : Matrix n n ℂ ↦ A * Aᴴ))).integral_eq
    have hB := ((hYIdent j).comp
      (by fun_prop : Measurable (fun A : Matrix n n ℂ ↦ Aᴴ * A))).integral_eq
    simp only [Function.comp_apply] at hA hB
    simpa only [D, σ2, hA, hB] using hh
  have hb := probability_hermitian_bernstein_of_variance_le D hDm hDIndep hDherm hDmean
    hR (mul_nonneg hℓR.le ht) hσ hDbound hDvariance
  have havg (ω : Ω) : (ℓ : ℝ)⁻¹ • ∑ j, Y j ω = (ℓ : ℝ)⁻¹ • ∑ j, X j ω - μ := by
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ hℓR.ne', one_smul]
  have hsub : {ω | t ≤ ‖(ℓ : ℝ)⁻¹ • ∑ j, X j ω - μ‖} ⊆
      {ω | ∃ x ∈ spectrum ℝ (∑ j, D j ω), (ℓ : ℝ) * t ≤ x} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [← havg ω, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓR.le),
      inv_mul_eq_div, le_div_iff₀ hℓR, mul_comm t] at hω
    refine ⟨‖∑ j, Y j ω‖, ?_, hω⟩
    rw [show (∑ j, D j ω) = hermitianDilation (∑ j, Y j ω) from
      (hermitianDilation_sum (fun j ↦ Y j ω)).symm]
    exact norm_mem_spectrum_hermitianDilation _
  calc
    _ ≤ P.real {ω | ∃ x ∈ spectrum ℝ (∑ j, D j ω), (ℓ : ℝ) * t ≤ x} :=
      measureReal_mono hsub
    _ ≤ (Fintype.card (n ⊕ n) : ℝ) * Real.exp
        (-(((ℓ : ℝ) * t) ^ 2) / (2 * (ℓ : ℝ) * σ2 + 2 * R * ((ℓ : ℝ) * t) / 3)) := hb
    _ = _ := by
      rw [Fintype.card_sum, Nat.cast_add, ← two_mul]
      congr 2
      rw [show 2 * (ℓ : ℝ) * σ2 + 2 * R * ((ℓ : ℝ) * t) / 3 =
          (ℓ : ℝ) * (2 * σ2 + 2 * R * t / 3) by ring,
        show -(((ℓ : ℝ) * t) ^ 2) = (ℓ : ℝ) * (-((ℓ : ℝ) * t ^ 2)) by ring,
        mul_div_mul_left _ _ hℓR.ne']

end Matrix
