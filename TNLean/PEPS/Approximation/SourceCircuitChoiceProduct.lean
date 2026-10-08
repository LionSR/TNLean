/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceChoiceCost
import TNLean.PEPS.Approximation.SourceCircuitLocations

/-! # Products of the exact scalar costs at touched gate occurrences -/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-choice-cost.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

open Classical in
private theorem sum_norm_coefficient_eq_prod_ite (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) :
    (∑ ξ : Choices A w, ‖coefficient A w ξ‖) =
      ∏ g : gateLocations w,
        if IsTouched A w g then ∑ ξ : branchLabels w g, ‖branchCoefficient w g ξ‖
        else 1 := by
  induction w with
  | id a =>
      rw [sum_norm_coefficient_id]
      change 1 = ∏ _ : Empty, _
      simp
  | comp w v ihw ihv =>
      rw [sum_norm_coefficient_comp, ihw, ihv]
      change _ = ∏ g : gateLocations w ⊕ gateLocations v, _
      rw [Fintype.prod_sum_type]
      rfl
  | localMap p ha hb T tail =>
      rw [sum_norm_coefficient_localMap]
      change 1 = ∏ _ : Empty, _
      simp
  | @gate C ι _ _ owner a b c G tail =>
      change _ = ∏ g : Unit,
        if IsTouched A (.gate owner G tail) g then ∑ ξ : ι, ‖c ξ‖ else 1
      simp only [Fintype.prod_unique]
      rw [isTouched_gate_iff]
      by_cases h : ∃ p : C, A (owner p) = true
      · rw [ite_eq_left h, sum_norm_coefficient_gate_of_touches _ _ _ _ h]
      · rw [ite_eq_right h, sum_norm_coefficient_gate_of_exterior _ _ _ _ h]
  | swap r s tail =>
      rw [sum_norm_coefficient_swap]
      change 1 = ∏ _ : Empty, _
      simp
  | frame r w ih => exact ih

open Classical in
/-- The total absolute coefficient factors over the actual touched gate
occurrences. Repeated uses of one gate remain separate factors, while untouched
gates contribute no factor.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_eq_prod (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) :
    (∑ ξ : Choices A w, ‖coefficient A w ξ‖) =
      ∏ g ∈ Finset.univ.filter (IsTouched A w),
        ∑ ξ : branchLabels w g, ‖branchCoefficient w g ξ‖ := by
  rw [Finset.prod_filter]
  exact sum_norm_coefficient_eq_prod_ite A w

open Classical in
/-- A bound on each touched gate's coefficient sum gives one factor of the
bound per touched occurrence. Empty touched sets have cost one.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_le_pow_card (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (B : ℝ)
    (hB : ∀ g, IsTouched A w g → ∑ ξ : branchLabels w g, ‖branchCoefficient w g ξ‖ ≤ B) :
    (∑ ξ : Choices A w, ‖coefficient A w ξ‖) ≤
      B ^ (Finset.univ.filter (IsTouched A w)).card := by
  rw [sum_norm_coefficient_eq_prod]
  calc
    _ ≤ ∏ _g ∈ Finset.univ.filter (IsTouched A w), B := by
      apply Finset.prod_le_prod₀
      · intro g _
        exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      · intro g hg
        exact hB g (Finset.mem_filter.mp hg).2
    _ = _ := by simp

open Classical in
/-- Independent ket and bra choices square the product of absolute coefficient
sums, retaining the complex conjugation in each original density coefficient.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_mul_conj_eq_prod_sq (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) :
    (∑ ξ : Choices A w, ∑ ζ : Choices A w,
      ‖coefficient A w ξ * star (coefficient A w ζ)‖) =
      (∏ g ∈ Finset.univ.filter (IsTouched A w),
        ∑ ξ : branchLabels w g, ‖branchCoefficient w g ξ‖) ^ 2 := by
  simp only [norm_mul, norm_star, ← Finset.sum_mul_sum]
  rw [← pow_two, sum_norm_coefficient_eq_prod]

open Classical in
/-- The ket–bra coefficient cost has two factors of the bound per touched gate
occurrence. No coefficient is charged at an untouched gate.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_mul_conj_le_pow_card (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) (B : ℝ)
    (hB : ∀ g, IsTouched A w g → ∑ ξ : branchLabels w g, ‖branchCoefficient w g ξ‖ ≤ B) :
    (∑ ξ : Choices A w, ∑ ζ : Choices A w,
      ‖coefficient A w ξ * star (coefficient A w ζ)‖) ≤
      B ^ (2 * (Finset.univ.filter (IsTouched A w)).card) := by
  calc
    _ = (∑ ξ : Choices A w, ‖coefficient A w ξ‖) ^ 2 := by
      simp only [norm_mul, norm_star, ← Finset.sum_mul_sum, pow_two]
    _ ≤ (B ^ (Finset.univ.filter (IsTouched A w)).card) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
        (sum_norm_coefficient_le_pow_card A w B hB) 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

end TNLean.PEPS.PairEffect.SourceCircuit
