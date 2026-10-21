/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Finprod
import TNLean.PEPS.AreaLaw.Geometry.PolynomialBudget
import TNLean.PEPS.AreaLaw.Geometry.RepairInitialMarkFacts

/-!
# Uniform weighted sums over the actual initial repair marks

Fix a real exponent. One positive numerical budget bounds every weighted sum
over the actual initial repair marks when each root's scale gives the stated
polynomial upper bound on its weight. The budget is chosen before the
coefficient, origin, domain, cut, width, lower layer, and weights.

The selected cells and marks are those of the existing joint initial choice.
The coefficient 576 is the product of the nine-mark bound and the sparse-cell
coefficient 64. The sum is written as a finite-support sum over the actual
initial carrier; its finiteness follows from the chosen finite mark set.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, sparse belt cells and initial marks,
lines 212–233 and 325–363; `geometry:total-repairs`, lines 668–692,
especially the weighted sum in lines 683–692.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open scoped BigOperators
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- **Weighted sums over the actual initial roots, with an explicit budget.**
The weight hypothesis uses the actual root scale and applies at every
admissible upper layer; the budget is `polynomialDyadicBudget P`.
Source: area-law Section 11, lines 212–233 and 325–363;
`geometry:total-repairs`, lines 668–692, especially 683–692. -/
theorem initialRepairStage_weighted_sum_le (P : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
    (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) :
    let D := initialRepairStage o Λ A C k₀ hC h₀
    ∀ (w : D.markIndex → ℝ),
      (∀ (p : D.markIndex) (k : ℕ), k₀ ≤ k →
        D.scale p ≤ (2 : ℝ) ^ k → w p ≤ c * ((k : ℝ) + 1) ^ P) →
      (∑ᶠ p : D.markIndex, w p) ≤
        576 * c * polynomialDyadicBudget P * (2 * (C : ℝ) + 1) ^ 2 *
          (edgeBoundary Λ A).card := by
  classical
  intro D w hw
  set B := polynomialDyadicBudget P
  have hbudget := sum_le_polynomialDyadicBudget P
  let : Fintype D.markIndex := by
    dsimp only [D, initialRepairStage]
    infer_instance
  rw [finsum_eq_sum_of_fintype]
  let F : ℕ → Finset (ℤ × ℤ) :=
    let hchoice := (Classical.choose_spec exists_uniform_separated_initial_marks).2
      o Λ A C k₀ hC h₀
    let a := Classical.choose hchoice
    let b := Classical.choose (Classical.choose_spec hchoice)
    fun k ↦ beltCellIndices
      (fineLayerIndices o k (fineScaleIndex k) (boundaryEndpoints Λ A) C)
      (2 ^ (pitchScaleIndex k - fineScaleIndex k)) (a k) (b k)
  obtain ⟨hFcard, _, hInc, _, _, hLocInj⟩ :=
    initialRepairStage_mark_spec o Λ A C k₀ hC h₀
  choose layer cell hlower hcell hloc hscale using fun p : D.markIndex ↦ (hInc p).2
  have hfiber (k : ℕ) :
      (Finset.univ.filter fun p : D.markIndex ↦ layer p = k).card ≤
        (beltMarks o (fineScaleIndex k) (F k)).card := by
    refine Finset.card_le_card_of_injOn D.location ?_ hLocInj.injOn
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with rfl
    exact Finset.mem_biUnion.mpr ⟨cell p, hcell p, hloc p⟩
  have hcount (k : ℕ) :
      (Finset.univ.filter fun p : D.markIndex ↦ layer p = k).card ≤ 9 * (F k).card :=
    (hfiber k).trans (card_beltMarks_le o (fineScaleIndex k) (F k))
  have hwlayer (p : D.markIndex) : w p ≤ c * ((layer p : ℝ) + 1) ^ P :=
    hw p (layer p) (hlower p) ((hscale p).le.trans
      (pow_le_pow_right₀ (by norm_num) (fineScaleIndex_le (layer p))))
  let K : Finset ℕ := Finset.univ.image layer
  have hgroup : ∑ p, w p =
      ∑ k ∈ K, ∑ p ∈ Finset.univ.filter (fun p : D.markIndex ↦ layer p = k), w p :=
    (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := K) (g := layer)
      (fun p _ ↦ Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩) w).symm
  have hsumlayer (k : ℕ) :
      (∑ p ∈ Finset.univ.filter (fun p : D.markIndex ↦ layer p = k), w p) ≤
        ((Finset.univ.filter (fun p : D.markIndex ↦ layer p = k)).card : ℝ) *
          (c * ((k : ℝ) + 1) ^ P) := by
    simpa only [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul (Finset.univ.filter (fun p : D.markIndex ↦ layer p = k))
        w (c * ((k : ℝ) + 1) ^ P)
        (fun p hp ↦ (Finset.mem_filter.mp hp).2 ▸ hwlayer p)
  have hcap_nonneg (k : ℕ) : 0 ≤ c * ((k : ℝ) + 1) ^ P :=
    mul_nonneg hc (Real.rpow_nonneg (by positivity) P)
  have hcount_real (k : ℕ) :
      ((Finset.univ.filter (fun p : D.markIndex ↦ layer p = k)).card : ℝ) ≤
        9 * ((F k).card : ℝ) := by
    exact_mod_cast hcount k
  have hsumcount (k : ℕ) :
      (∑ p ∈ Finset.univ.filter (fun p : D.markIndex ↦ layer p = k), w p) ≤
        (9 * ((F k).card : ℝ)) * (c * ((k : ℝ) + 1) ^ P) :=
    (hsumlayer k).trans (mul_le_mul_of_nonneg_right (hcount_real k) (hcap_nonneg k))
  have hsparse (k : ℕ) :
      (9 * ((F k).card : ℝ)) * (c * ((k : ℝ) + 1) ^ P) ≤
        (9 * (64 * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
          (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * k / 2))) *
            (c * ((k : ℝ) + 1) ^ P) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hFcard k) (by norm_num)) (hcap_nonneg k)
  have hrow (k : ℕ) :
      (∑ p ∈ Finset.univ.filter (fun p : D.markIndex ↦ layer p = k), w p) ≤
        576 * c * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card *
          (((k : ℝ) + 1) ^ P *
            (2 : ℝ) ^ (-(Exponents.geometryDelta : ℝ) * k / 2)) := by
    convert (hsumcount k).trans (hsparse k) using 1
    ring
  rw [hgroup]
  refine (Finset.sum_le_sum (fun k _ ↦ hrow k)).trans ?_
  rw [← Finset.mul_sum]
  convert mul_le_mul_of_nonneg_left (hbudget K)
    (show 0 ≤ 576 * c * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card by
      positivity) using 1
  ring

/-- A numerical budget for weighted sums over the actual initial roots,
chosen before the coefficient and all geometric data. The weight hypothesis
uses the actual root scale and applies at every admissible upper layer. The
budget is `polynomialDyadicBudget P` (`initialRepairStage_weighted_sum_le`).
Source: area-law Section 11, lines 212–233 and 325–363;
`geometry:total-repairs`, lines 668–692, especially 683–692. -/
theorem exists_uniform_initialRepairStage_weighted_sum_bound (P : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (c : ℝ), 0 ≤ c →
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀),
        let D := initialRepairStage o Λ A C k₀ hC h₀
        ∀ (w : D.markIndex → ℝ),
          (∀ (p : D.markIndex) (k : ℕ), k₀ ≤ k →
            D.scale p ≤ (2 : ℝ) ^ k → w p ≤ c * ((k : ℝ) + 1) ^ P) →
          (∑ᶠ p : D.markIndex, w p) ≤
            576 * c * B * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card :=
  ⟨_, polynomialDyadicBudget_pos P, fun _ hc ↦ initialRepairStage_weighted_sum_le P hc⟩

end TNLean.PEPS.AreaLaw.Geometry
