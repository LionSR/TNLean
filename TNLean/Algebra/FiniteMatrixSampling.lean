/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FiniteMatrixMoments

/-!
# Finite tails and sample existence for matrix averages

The finite uniform moment estimate gives a Markov bound for the fraction of
assignments whose sample mean has norm at least a prescribed threshold. If
that fraction is strictly below one, an assignment with smaller norm exists.
An explicit sufficient count is `ℓ η² ≥ 4p²R²`, with `N < 4^p`.

For a general family of matrices of norm at most `R`, subtracting its uniform
mean gives centered matrices of norm at most `2R`. The corresponding sample
count is `ℓ η² ≥ 16p²R²`. All means and fractions are exact finite sums.

These are auxiliary finite sampling results for LVV, arXiv:1307.5143v1,
Section 2.3.1. The sharp matrix Bernstein theorem and the construction of the
source's sampled operator remain separate results. The ground-energy
dependence of that construction is recorded in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

open Classical in
/-- A finite Markov bound for centered matrix samples: the fraction of sample assignments
whose mean has norm at least `η` is at most `card n * (p² R² / (card β * η²))^p`.
This is an auxiliary finite sampling estimate for LVV, arXiv:1307.5143v1, Section 2.3.1. -/
theorem finite_uniform_tail_bound_of_centered {α β n : Type*} [Fintype α] [Fintype β]
    [Fintype n] [DecidableEq n] [Nonempty α] [Nonempty β] [Nonempty n]
    (X : β → α → Matrix n n ℂ) {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η)
    (hX : ∀ b a, ‖X b a‖ ≤ R) (hmean : ∀ b, ∑ a, X b a = 0)
    {p : ℕ} (hp : 0 < p) :
    ((Finset.univ.filter fun σ : β → α ↦
        η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, X b (σ b)‖).card : ℝ) /
        (Fintype.card (β → α) : ℝ) ≤
      (Fintype.card n : ℝ) *
        ((p : ℝ) ^ 2 * R ^ 2 / ((Fintype.card β : ℝ) * η ^ 2)) ^ p := by
  classical
  let f (σ : β → α) : ℝ := ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, X b (σ b)‖
  let bad : Finset (β → α) := Finset.univ.filter fun σ ↦ η ≤ f σ
  have hM : 0 < (Fintype.card (β → α) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hηpow : 0 < η ^ (2 * p) := pow_pos hη _
  have hmarkov : (bad.card : ℝ) * η ^ (2 * p) ≤ ∑ σ : β → α, f σ ^ (2 * p) := by
    calc
      _ = ∑ _σ ∈ bad, η ^ (2 * p) := by simp
      _ ≤ ∑ σ ∈ bad, f σ ^ (2 * p) := Finset.sum_le_sum fun σ hσ ↦
        pow_le_pow_left₀ hη.le (Finset.mem_filter.mp hσ).2 _
      _ ≤ ∑ σ : β → α, f σ ^ (2 * p) := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun σ _ _ ↦ by positivity)
  have hmoment : (∑ σ : β → α, f σ ^ (2 * p)) ≤
      ((Fintype.card n : ℝ) * ((p : ℝ) ^ 2 * R ^ 2 / (Fintype.card β : ℝ)) ^ p) *
        (Fintype.card (β → α) : ℝ) :=
    (div_le_iff₀ hM).mp (average_norm_average_pow_le_of_centered X hR hX hmean hp)
  have hfrac : (bad.card : ℝ) / (Fintype.card (β → α) : ℝ) ≤
      ((Fintype.card n : ℝ) * ((p : ℝ) ^ 2 * R ^ 2 / (Fintype.card β : ℝ)) ^ p) /
        η ^ (2 * p) := by
    apply (div_le_iff₀ hM).mpr
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hηpow).mpr (hmarkov.trans hmoment)
  calc
    _ ≤ ((Fintype.card n : ℝ) * ((p : ℝ) ^ 2 * R ^ 2 / (Fintype.card β : ℝ)) ^ p) /
        η ^ (2 * p) := hfrac
    _ = _ := by
      simp only [mul_pow, ← pow_mul, div_eq_mul_inv, mul_inv]
      ring

end Matrix

namespace Matrix

open Classical in
/-- A centered family has a sample mean of norm below `η` when its finite tail bound is
strictly less than one. Supporting finite sampling in LVV, arXiv:1307.5143v1, Section 2.3.1. -/
theorem exists_average_norm_lt_of_centered {α β n : Type*} [Fintype α] [Fintype β]
    [Fintype n] [DecidableEq n] [Nonempty α] [Nonempty β] [Nonempty n]
    (X : β → α → Matrix n n ℂ) {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η)
    (hX : ∀ b a, ‖X b a‖ ≤ R) (hmean : ∀ b, ∑ a, X b a = 0)
    {p : ℕ} (hp : 0 < p)
    (hsmall : (Fintype.card n : ℝ) *
      ((p : ℝ) ^ 2 * R ^ 2 / ((Fintype.card β : ℝ) * η ^ 2)) ^ p < 1) :
    ∃ σ : β → α, ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, X b (σ b)‖ < η := by
  classical
  by_contra h
  have hall (σ : β → α) : η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, X b (σ b)‖ :=
    not_lt.mp (fun hc ↦ h ⟨σ, hc⟩)
  have hbad : (Finset.univ.filter fun σ : β → α ↦
      η ≤ ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, X b (σ b)‖) = Finset.univ := by
    ext σ
    simp [hall σ]
  have htail := finite_uniform_tail_bound_of_centered X hR hη hX hmean hp
  have hM : (Fintype.card (β → α) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hbad, Finset.card_univ, div_self hM] at htail
  exact (not_le_of_gt hsmall) htail

open Classical in
/-- Explicit sample count for centered finite matrix families. It suffices that
`card n < 4^p` and `4p²R² ≤ card β * η²`. Supporting finite sampling in LVV,
arXiv:1307.5143v1, Section 2.3.1. -/
theorem exists_average_norm_lt_of_sample_card {α β n : Type*} [Fintype α] [Fintype β]
    [Fintype n] [DecidableEq n] [Nonempty α] [Nonempty β] [Nonempty n]
    (X : β → α → Matrix n n ℂ) {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η)
    (hX : ∀ b a, ‖X b a‖ ≤ R) (hmean : ∀ b, ∑ a, X b a = 0)
    {p : ℕ} (hp : 0 < p) (hN : (Fintype.card n : ℝ) < (4 : ℝ) ^ p)
    (hcard : 4 * (p : ℝ) ^ 2 * R ^ 2 ≤ (Fintype.card β : ℝ) * η ^ 2) :
    ∃ σ : β → α, ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, X b (σ b)‖ < η := by
  classical
  apply exists_average_norm_lt_of_centered X hR hη hX hmean hp
  have hℓ : 0 < (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos
  have hden : 0 < (Fintype.card β : ℝ) * η ^ 2 := mul_pos hℓ (sq_pos_of_pos hη)
  have hratio : (p : ℝ) ^ 2 * R ^ 2 / ((Fintype.card β : ℝ) * η ^ 2) ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hpow := pow_le_pow_left₀
    (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hden.le) hratio p
  calc
    _ ≤ (Fintype.card n : ℝ) * (1 / 4 : ℝ) ^ p :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
    _ = (Fintype.card n : ℝ) / (4 : ℝ) ^ p := by simp only [div_eq_mul_inv, one_mul, inv_pow]
    _ < 1 := (div_lt_one (pow_pos (by norm_num) p)).mpr hN

end Matrix

namespace Matrix

open Classical in
/-- A bounded finite matrix family has a sample average within `η` of its uniform mean.
The centered samples have norm at most `2R`, so the sufficient count is
`16p²R² ≤ card β * η²`, with `card n < 4^p`. Supporting finite sampling in LVV,
arXiv:1307.5143v1, Section 2.3.1; the source's sampled operator and its bond estimates
are separate results. -/
theorem exists_average_sub_mean_norm_lt {α β n : Type*} [Fintype α] [Fintype β]
    [Fintype n] [DecidableEq n] [Nonempty α] [Nonempty β] [Nonempty n]
    (Y : α → Matrix n n ℂ) {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η)
    (hY : ∀ a, ‖Y a‖ ≤ R) {p : ℕ} (hp : 0 < p)
    (hN : (Fintype.card n : ℝ) < (4 : ℝ) ^ p)
    (hcard : 16 * (p : ℝ) ^ 2 * R ^ 2 ≤ (Fintype.card β : ℝ) * η ^ 2) :
    ∃ σ : β → α,
      ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) -
        (Fintype.card α : ℂ)⁻¹ • ∑ a, Y a‖ < η := by
  classical
  let μ : Matrix n n ℂ := (Fintype.card α : ℂ)⁻¹ • ∑ a, Y a
  have hαR : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hαC : (Fintype.card α : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβC : (Fintype.card β : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ‖∑ a, Y a‖ ≤ (Fintype.card α : ℝ) * R := by
    calc
      _ ≤ ∑ a, ‖Y a‖ := norm_sum_le _ _
      _ ≤ ∑ _a : α, R := Finset.sum_le_sum fun a _ ↦ hY a
      _ = _ := by simp
  have hμ : ‖μ‖ ≤ R := by
    calc
      _ = (Fintype.card α : ℝ)⁻¹ * ‖∑ a, Y a‖ := by
        simp only [μ, norm_smul, norm_inv, Complex.norm_natCast]
      _ ≤ (Fintype.card α : ℝ)⁻¹ * ((Fintype.card α : ℝ) * R) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = R := by rw [← mul_assoc, inv_mul_cancel₀ hαR, one_mul]
  have hcenter : ∑ a, (Y a - μ) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, μ, smul_smul, mul_inv_cancel₀ hαC, one_smul, sub_self]
  have hXY (_b : β) (a : α) : ‖Y a - μ‖ ≤ 2 * R := by
    calc
      _ ≤ ‖Y a‖ + ‖μ‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hY a) hμ
      _ = _ := by ring
  have hcard' : 4 * (p : ℝ) ^ 2 * (2 * R) ^ 2 ≤ (Fintype.card β : ℝ) * η ^ 2 := by
    nlinarith only [hcard]
  obtain ⟨σ, hσ⟩ := exists_average_norm_lt_of_sample_card
    (fun (_b : β) a ↦ Y a - μ) (mul_nonneg (by norm_num) hR) hη hXY
    (fun _ ↦ hcenter) hp hN hcard'
  have hexpand : (Fintype.card β : ℂ)⁻¹ • ∑ b, (Y (σ b) - μ) =
      (Fintype.card β : ℂ)⁻¹ • ∑ b, Y (σ b) - μ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hβC, one_smul]
  exact ⟨σ, by simpa only [hexpand] using hσ⟩

end Matrix
