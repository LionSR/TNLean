/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteHermitianBernstein
import TNLean.Algebra.HermitianDilation

/-!
# Finite uniform rectangular matrix Bernstein inequality

Independent uniform samples from a finite centered rectangular matrix family satisfy
the operator-norm Bernstein bound. Its variance is the maximum of the two averaged
Gram-matrix norms, and its dimension factor is the sum of the row and column
cardinalities. The square-matrix corollary centers the given family at its actual
uniform mean and has the factor `2d` used by LVV.

**Scope restriction (finite uniform samples):** These theorems are finite uniform
specializations of Tropp, *User-friendly tail bounds for sums of random matrices*,
Theorem 1.6, and of LVV, arXiv:1307.5143v1, Theorem 2.13. The general probability
formulation remains to be proved. The scope and extension plan are recorded in
`docs/paper-gaps/finite_uniform_matrix_bernstein.tex`.

The proof derives the Hermitian dilation, its norm and spectral endpoint, and its
variance bound. No concentration estimate or dilation identity is added as a
hypothesis. The source is:
https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

open Classical in
/-- The finite uniform rectangular Bernstein bound for the norm of a sum.
This is the finite uniform specialization of Tropp, Theorem 1.6. -/
theorem finite_uniform_rectangular_bernstein
    {α m n : Type*} [Fintype α] [Nonempty α] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]
    (Y : α → Matrix m n ℂ) (hmean : ∑ a, Y a = 0) {R τ : ℝ}
    (hR : 0 ≤ R) (hτ : 0 ≤ τ) (hnorm : ∀ a, ‖Y a‖ ≤ R) (ℓ : ℕ) :
    ((Finset.univ.filter fun σ : Fin ℓ → α ↦ τ ≤ ‖∑ j, Y (σ j)‖).card : ℝ) /
        (Fintype.card (Fin ℓ → α) : ℝ) ≤
      (Fintype.card m + Fintype.card n : ℝ) * Real.exp
        (-(τ ^ 2) / (2 * (ℓ : ℝ) *
          max ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, Y a * (Y a)ᴴ‖
            ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, (Y a)ᴴ * Y a‖ + 2 * R * τ / 3)) := by
  classical
  have hDmean : ∑ a, hermitianDilation (Y a) = 0 := by
    rw [← hermitianDilation_sum, hmean]
    simp only [hermitianDilation, conjTranspose_zero, fromBlocks_zero]
  have hDnorm (a : α) : ‖hermitianDilation (Y a)‖ ≤ R := by
    simpa only [norm_hermitianDilation] using hnorm a
  have ht := finite_uniform_hermitian_bernstein_of_variance_le
    (fun a ↦ hermitianDilation (Y a)) (fun a ↦ isHermitian_hermitianDilation (Y a))
    hDmean hR hτ hDnorm (norm_average_hermitianDilation_sq_le Y) ℓ
  have hsub : (Finset.univ.filter fun σ : Fin ℓ → α ↦ τ ≤ ‖∑ j, Y (σ j)‖) ⊆
      (Finset.univ.filter fun σ : Fin ℓ → α ↦
        ∃ x ∈ spectrum ℝ (∑ j, hermitianDilation (Y (σ j))), τ ≤ x) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    refine ⟨‖∑ j, Y (σ j)‖, ?_, hσ⟩
    rw [← hermitianDilation_sum]
    exact norm_mem_spectrum_hermitianDilation _
  calc
    _ ≤ ((Finset.univ.filter fun σ : Fin ℓ → α ↦
        ∃ x ∈ spectrum ℝ (∑ j, hermitianDilation (Y (σ j))), τ ≤ x).card : ℝ) /
        (Fintype.card (Fin ℓ → α) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (Nat.cast_nonneg _)
    _ ≤ _ := by simpa only [Fintype.card_sum, Nat.cast_add] using ht

open Classical in
/-- The finite uniform rectangular Bernstein bound for the sample mean.
This is the normalized finite uniform specialization of Tropp, Theorem 1.6. -/
theorem finite_uniform_rectangular_average_bernstein
    {α m n : Type*} [Fintype α] [Nonempty α] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n]
    (Y : α → Matrix m n ℂ) (hmean : ∑ a, Y a = 0) {R t : ℝ}
    (hR : 0 ≤ R) (ht : 0 ≤ t) (hnorm : ∀ a, ‖Y a‖ ≤ R) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ((Finset.univ.filter fun σ : Fin ℓ → α ↦
        t ≤ ‖(ℓ : ℝ)⁻¹ • ∑ j, Y (σ j)‖).card : ℝ) /
        (Fintype.card (Fin ℓ → α) : ℝ) ≤
      (Fintype.card m + Fintype.card n : ℝ) * Real.exp
        (-((ℓ : ℝ) * t ^ 2) /
          (2 * max ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, Y a * (Y a)ᴴ‖
            ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, (Y a)ᴴ * Y a‖ + 2 * R * t / 3)) := by
  classical
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hfilter : (Finset.univ.filter fun σ : Fin ℓ → α ↦
      t ≤ ‖(ℓ : ℝ)⁻¹ • ∑ j, Y (σ j)‖) =
      (Finset.univ.filter fun σ : Fin ℓ → α ↦ (ℓ : ℝ) * t ≤ ‖∑ j, Y (σ j)‖) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓR.le),
      inv_mul_eq_div, le_div_iff₀ hℓR, mul_comm t]
  rw [hfilter]
  have hb := finite_uniform_rectangular_bernstein Y hmean hR (mul_nonneg hℓR.le ht) hnorm ℓ
  convert hb using 1
  congr 2
  let V := max ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, Y a * (Y a)ᴴ‖
    ‖(Fintype.card α : ℝ)⁻¹ • ∑ a, (Y a)ᴴ * Y a‖
  change -((ℓ : ℝ) * t ^ 2) / (2 * V + 2 * R * t / 3) =
    -(((ℓ : ℝ) * t) ^ 2) / (2 * (ℓ : ℝ) * V + 2 * R * ((ℓ : ℝ) * t) / 3)
  rw [show 2 * (ℓ : ℝ) * V + 2 * R * ((ℓ : ℝ) * t) / 3 =
      (ℓ : ℝ) * (2 * V + 2 * R * t / 3) by ring,
    show -(((ℓ : ℝ) * t) ^ 2) = (ℓ : ℝ) * (-((ℓ : ℝ) * t ^ 2)) by ring,
    mul_div_mul_left _ _ hℓR.ne']

end Matrix

namespace Matrix

open Classical in
/-- A square matrix family concentrates about its actual uniform mean, with dimension
factor `2d` and the maximum of its two centered Gram-matrix variance norms.
This is the finite uniform specialization of LVV, Theorem 2.13, quoted from Tropp, Theorem 1.6. -/
theorem finite_uniform_matrix_average_sub_mean_bernstein
    {α n : Type*} [Fintype α] [Nonempty α] [Fintype n] [DecidableEq n] [Nonempty n]
    (X : α → Matrix n n ℂ) {R t : ℝ} (ht : 0 ≤ t)
    (hnorm : ∀ a, ‖X a - (Fintype.card α : ℝ)⁻¹ • ∑ b, X b‖ ≤ R)
    {ℓ : ℕ} (hℓ : 0 < ℓ) :
    ((Finset.univ.filter fun σ : Fin ℓ → α ↦
        t ≤ ‖(ℓ : ℝ)⁻¹ • ∑ j, X (σ j) - (Fintype.card α : ℝ)⁻¹ • ∑ a, X a‖).card : ℝ) /
        (Fintype.card (Fin ℓ → α) : ℝ) ≤
      2 * (Fintype.card n : ℝ) * Real.exp
        (-((ℓ : ℝ) * t ^ 2) /
          (2 * max
            ‖(Fintype.card α : ℝ)⁻¹ • ∑ a,
              (X a - (Fintype.card α : ℝ)⁻¹ • ∑ b, X b) *
                (X a - (Fintype.card α : ℝ)⁻¹ • ∑ b, X b)ᴴ‖
            ‖(Fintype.card α : ℝ)⁻¹ • ∑ a,
              (X a - (Fintype.card α : ℝ)⁻¹ • ∑ b, X b)ᴴ *
                (X a - (Fintype.card α : ℝ)⁻¹ • ∑ b, X b)‖ + 2 * R * t / 3)) := by
  classical
  let μ : Matrix n n ℂ := (Fintype.card α : ℝ)⁻¹ • ∑ a, X a
  let Y (a : α) := X a - μ
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hmean : ∑ a, Y a = 0 := by
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ, μ, smul_smul, mul_inv_cancel₀ hα, one_smul, sub_self]
  have hYnorm : ∀ a, ‖Y a‖ ≤ R := hnorm
  have hR : 0 ≤ R := (norm_nonneg (Y (Classical.choice inferInstance))).trans
    (hYnorm (Classical.choice inferInstance))
  have heq (σ : Fin ℓ → α) : (ℓ : ℝ)⁻¹ • ∑ j, Y (σ j) =
      (ℓ : ℝ)⁻¹ • ∑ j, X (σ j) - μ := by
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ hℓR, one_smul]
  have hb := finite_uniform_rectangular_average_bernstein Y hmean hR ht hYnorm hℓ
  simpa only [heq, μ, Y, show (Fintype.card n : ℝ) + Fintype.card n =
    2 * (Fintype.card n : ℝ) by ring] using hb

end Matrix
