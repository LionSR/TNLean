/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Algorithm.ValidOracleCost

/-!
# Theorem 1: polynomial time in the chain length and the accuracy

The accuracy parameter `R` of the ground-state program is chosen from the accuracy `η`:
with `R = max 1 ⌈√(4 L / (Δ η))⌉`, the overlap `1 - 4 L / (R² Δ)` is at least `1 - η`, and
`L + 2 R² + 1 ≤ 17 L / (Δ η) + 5 L`, so the cost bound `P (L + 2 R² + 1)^d` is a polynomial
in `L` and `1 / η`. Both statements hold for every valid oracle.

The degree of `1 / η` is the degree `d` of the whole computation, which depends on the local
dimension and the gap. The printed `n^{c(d, ε)} poly(n / η)` of Landau, Vazirani and Vidick
does not say so, but their proof has the same feature: the final error reduction at precision
`η / n` has `d^{2κ log(n / η)}` terms with `κ = O(1 / ε)` (lines 580--592 and 669--671), so its
degree in `1 / η` is of order `log d / ε`. Recorded in `docs/paper-gaps/lvv13_cost_model.tex`.

**Scope restriction (cost model):** the bound is on the declared oracle cost
`FreeM.cost o queryCost`, not a proved running time of an implementation: each query is charged
a declared polynomial cost in the dimensions of its arguments, arithmetic is exact, and nothing
is proved about how a query is answered; see `docs/paper-gaps/lvv13_cost_model.tex`.

**Scope restriction (quantitative constants):** the size and bond budgets use the library
constant-cut bond `constantCutBond` and the corrected net exponent, not the printed quantitative
bounds; see `docs/paper-gaps/lvv13_constant_bond.tex`.

**Local fix (trimming radius):** bond trimming uses the corrected quadratic radius
`bondTrimmingRadius` recorded at
<https://sirui-lu.com/QICLean/paper-gaps/lvv13_trimming_radius.pdf>.

Source: LVV13, arXiv:1307.5143v1, `algo53.tex`, lines 213--216.
-/

open Matrix Cslib
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace TNLean.MPS.AreaLaw

variable {q : ℕ}

open LinearAlgebraQuery

/-- The accuracy parameter for accuracy `η`: `max 1 ⌈√(4 L / (Δ η))⌉`. -/
noncomputable def lvvAccuracyParameter (L : ℕ) (Δ η : ℝ) : ℕ :=
  max 1 ⌈Real.sqrt (4 * L / (Δ * η))⌉₊

theorem one_le_lvvAccuracyParameter (L : ℕ) (Δ η : ℝ) : 1 ≤ lvvAccuracyParameter L Δ η :=
  le_max_left _ _

/-- The accuracy parameter gives overlap at least `1 - η`. -/
theorem four_mul_div_lvvAccuracyParameter_le {L : ℕ} {Δ η : ℝ} (hΔ : 0 < Δ) (hη : 0 < η) :
    4 * L / ((lvvAccuracyParameter L Δ η : ℝ) ^ 2 * Δ) ≤ η := by
  set x : ℝ := 4 * L / (Δ * η) with hx
  have hx0 : 0 ≤ x := by positivity
  have hR : Real.sqrt x ≤ (lvvAccuracyParameter L Δ η : ℝ) := by
    calc
      Real.sqrt x ≤ (⌈Real.sqrt x⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (lvvAccuracyParameter L Δ η : ℝ) := by
        exact_mod_cast le_max_right 1 ⌈Real.sqrt x⌉₊
  have hR2 : x ≤ (lvvAccuracyParameter L Δ η : ℝ) ^ 2 := by
    calc
      x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx0).symm
      _ ≤ (lvvAccuracyParameter L Δ η : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg x) hR 2
  have hRpos : (0 : ℝ) < (lvvAccuracyParameter L Δ η : ℝ) ^ 2 := by
    have := one_le_lvvAccuracyParameter L Δ η
    positivity
  rw [div_le_iff₀ (by positivity)]
  have : 4 * (L : ℝ) = x * (Δ * η) := by
    rw [hx, div_mul_cancel₀ _ (by positivity)]
  rw [this]
  calc
    x * (Δ * η) = η * (x * Δ) := by ring
    _ ≤ η * ((lvvAccuracyParameter L Δ η : ℝ) ^ 2 * Δ) := by gcongr

/-- The padded chain length is at most `17 L / (Δ η) + 5 L` for `L ≥ 1`, `Δ η ≤ 1`. -/
theorem padded_length_lvvAccuracyParameter_le {L : ℕ} (hL : 1 ≤ L) {Δ η : ℝ} (hΔ : 0 < Δ)
    (hη : 0 < η) (hΔη : Δ * η ≤ 1) :
    ((L + 2 * lvvAccuracyParameter L Δ η ^ 2 + 1 : ℕ) : ℝ) ≤ 17 * L / (Δ * η) + 5 * L := by
  set x : ℝ := 4 * L / (Δ * η) with hx
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    nlinarith
  have hx0 : 0 ≤ x := by linarith
  have hceil : (⌈Real.sqrt x⌉₊ : ℝ) ≤ Real.sqrt x + 1 :=
    (Nat.ceil_lt_add_one (Real.sqrt_nonneg x)).le
  have hsqrt1 : 1 ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0]
    linarith
  have hR : (lvvAccuracyParameter L Δ η : ℝ) ≤ Real.sqrt x + 1 := by
    unfold lvvAccuracyParameter
    push_cast
    exact max_le (by linarith) hceil
  have hR0 : (0 : ℝ) ≤ lvvAccuracyParameter L Δ η := Nat.cast_nonneg _
  have hR2 : (lvvAccuracyParameter L Δ η : ℝ) ^ 2 ≤ 2 * x + 2 := by
    calc
      (lvvAccuracyParameter L Δ η : ℝ) ^ 2 ≤ (Real.sqrt x + 1) ^ 2 := pow_le_pow_left₀ hR0 hR 2
      _ = x + 2 * Real.sqrt x + 1 := by
        rw [add_sq, Real.sq_sqrt hx0]
        ring
      _ ≤ 2 * x + 2 := by
        nlinarith [sq_nonneg (Real.sqrt x - 1), Real.sq_sqrt hx0]
  have hxL : x ≤ 4 * L / (Δ * η) := le_of_eq hx
  push_cast
  calc
    (L : ℝ) + 2 * (lvvAccuracyParameter L Δ η : ℝ) ^ 2 + 1
        ≤ L + 2 * (2 * x + 2) + 1 := by linarith
    _ = 4 * x + L + 5 := by ring
    _ ≤ 16 * L / (Δ * η) + L / (Δ * η) + 5 * L := by
      have h1 : 4 * x = 16 * L / (Δ * η) := by rw [hx]; ring
      have h2 : (L : ℝ) ≤ L / (Δ * η) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have h3 : (5 : ℝ) ≤ 5 * L := by linarith
      linarith
    _ = 17 * L / (Δ * η) + 5 * L := by ring

/-- **Theorem 1 with a polynomial in the chain length and the accuracy**, on the Gaussian
route, for every valid oracle.
Fix `q ≥ 2` and `Δ > 0`. There are `P ≥ 1` and `d` such that for every chain of `L ≥ 1`
sites, every accuracy `0 < η` with `Δ η ≤ 1`, every valid oracle and every ground pair with
gap `Δ`, the ground-state program at the accuracy parameter `R = max 1 ⌈√(4L/(Δη))⌉` outputs
a unit matrix product state with overlap at least `1 - η` with the ground state, and its
declared cost is at most `P (17 L / (Δ η) + 5 L)^d`, a polynomial in `L` and `1/η` with
exponent and coefficient depending on `q` and `Δ` alone, as in the source's proof; see the
module docstring. LVV13, `algo53.tex`, lines 213--216. -/
theorem exists_theorem_one_of_valid (hq : 2 ≤ q) {Delta : ℝ} (hDelta : 0 < Delta) :
    ∃ P d : ℕ, 1 ≤ P ∧ ∀ (o : {ι : Type} → LinearAlgebraQuery q ι → ι), IsValidOracle o →
      ∀ (L : ℕ), 1 ≤ L → ∀ {η : ℝ}, 0 < η → Delta * η ≤ 1 →
      ∀ (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
        (hs : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q) (h j)
          (interval L j.val (j.val + 2))) (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1),
      let R := lvvAccuracyParameter L Delta η
      let ψ := FreeM.eval o (groundStateProgram hq h hs h0 h1 Delta R)
      (∀ (E : ℝ) (Γ : EuclideanSpace ℂ (Fin L → Fin q)),
        IsGappedGroundState (∑ j, h j) E Γ Delta →
        ‖ψ‖ = 1 ∧ 1 - η ≤ ‖⟪Γ, ψ⟫_ℂ‖ ∧
          IsOpenMPS L q (lvvSuccessiveCardBound q (min Delta 1) (L + 2 * R ^ 2) *
            max 1 (lvvSuccessiveBondBound q (min Delta 1) (L + 2 * R ^ 2))) (fun x ↦ ψ x)) ∧
      ((FreeM.cost o queryCost (groundStateProgram hq h hs h0 h1 Delta R) : ℕ) : ℝ) ≤
        P * (17 * L / (Delta * η) + 5 * L) ^ d := by
  obtain ⟨P, d, hP, hcost⟩ := exists_groundStateProgram_cost_polynomial_of_valid hq hDelta
  refine ⟨P, d, hP, fun o hv L hL η hη hΔη h hs h0 h1 ↦ ?_⟩
  intro R ψ
  refine ⟨fun E Γ hgs ↦ ?_, ?_⟩
  · obtain ⟨hψ1, hover, hmps⟩ := groundStateProgram_spec_of_valid hv hL hq h hs h0 h1 hDelta
      (one_le_lvvAccuracyParameter L Delta η) E Γ hgs
    exact ⟨hψ1, le_trans (by linarith [four_mul_div_lvvAccuracyParameter_le (L := L) hDelta hη])
      hover, hmps⟩
  · have hc := (hcost o hv L R hL h hs h0 h1).2
    have hlen := padded_length_lvvAccuracyParameter_le hL hDelta hη hΔη
    calc
      ((FreeM.cost o queryCost (groundStateProgram hq h hs h0 h1 Delta R) : ℕ) : ℝ)
          ≤ ((P * (L + 2 * R ^ 2 + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hc
      _ = P * ((L + 2 * R ^ 2 + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
      _ ≤ P * (17 * L / (Delta * η) + 5 * L) ^ d := by
        gcongr

end TNLean.MPS.AreaLaw
