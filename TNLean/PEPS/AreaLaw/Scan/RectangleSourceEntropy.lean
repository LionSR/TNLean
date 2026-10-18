/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.WeakRectangleShellEntropy
import TNLean.PEPS.AreaLaw.Scan.PrefixBoundary
import Mathlib.Data.Nat.Log

/-!
# Current-exponent source entropy on a weakly safe rectangle

The same pointwise safe-box estimate supplies both the literal target and all
positive-depth prefixes of a rectangle. A fixed positive lower exponent makes
one coefficient work for every current exponent. The shell clearance is the
weak parent condition D0*size, with its derived collar budget, and the state is
unchanged.

Source: OpenAI area-law manuscript, `08-scanner.tex`, lines 705--729,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Validation and inherited-dependency scope:
`docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

/-- The coefficient `Cbox (24 + 64 / (2^b - 1) + 1)` of the rough-scanner target and prefix
inputs on a weakly safe rectangle, for a safe-box bound with coefficient `Cbox` at exponents
`e ≥ b`. Source: `08-scanner.tex`, lines 705--729. -/
noncomputable def weakRectangleSourceEntropyCoefficient (b Cbox : ℝ) : ℝ :=
  Cbox * (24 + 64 / ((2 : ℝ) ^ b - 1) + 1)

/-- The rectangle input coefficient is nonnegative. Source: `08-scanner.tex`, lines 705--729. -/
theorem weakRectangleSourceEntropyCoefficient_nonneg {b Cbox : ℝ} (hb : 0 < b)
    (hCbox : 0 ≤ Cbox) : 0 ≤ weakRectangleSourceEntropyCoefficient b Cbox := by
  have := sub_pos.mpr (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hb)
  unfold weakRectangleSourceEntropyCoefficient
  positivity

/-- The rough-scanner target and prefix inputs on a weakly safe rectangle hold with the explicit
coefficient `weakRectangleSourceEntropyCoefficient b Cbox`, for every current exponent `e ≥ b`
and every physical rectangle. Source: `08-scanner.tex`, lines 705--729. -/
theorem weakRectangle_source_entropy_bounds
    (b Cbox : ℝ) (hb : 0 < b) (hCbox : 0 ≤ Cbox) :
    ∀ (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q), ‖Ω‖ = 1 →
    ∀ (A : Finset (Site Λ)) (Q : IntRect) (hQ : Q.toFinset.Nonempty),
      IsSafe Λ A D₀ Q → ∀ n L : ℕ, Q.size ≤ n → 1 ≤ L → L ≤ Q.size →
      D₀ * L + L ≤ D₀ * Q.size →
      ∀ e : ℝ, b ≤ e →
      (∀ Q' : IntRect, IsSafe Λ A D₀ Q' →
        regionalEntropy Λ q Ω (rectRegion A Q') ≤ Cbox * (Q'.size : ℝ) ^ (1 + e)) →
      regionalEntropy Λ q Ω (rectRegion A Q) ≤
          weakRectangleSourceEntropyCoefficient b Cbox * (n : ℝ) ^ (1 + e) ∧
        ∀ j : ℕ, j ≤ L →
          regionalEntropy Λ q Ω
            (positiveDepthPrefix A (fun x ↦ ambientDepth Q.toFinset hQ x.val) (j : ℤ)) ≤
              weakRectangleSourceEntropyCoefficient b Cbox * ((n : ℝ) * (L : ℝ) ^ e + n) := by
  let Cshell := 24 + 64 / ((2 : ℝ) ^ b - 1)
  have hden : 0 < (2 : ℝ) ^ b - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hb)
  have hCshell : 0 ≤ Cshell := by dsimp only [Cshell]; positivity
  intro Λ q D₀ Ω hΩ A Q hQ hsafe n L hsize hLpos hL hbudget e hbe hbox
  have he : 0 < e := hb.trans_le hbe
  have hCtarget : Cbox ≤ Cbox * (Cshell + 1) := by nlinarith
  have hcoeff : Cbox * (24 + 64 / ((2 : ℝ) ^ e - 1)) ≤ Cbox * Cshell := by
    have hde : (2 : ℝ) ^ b - 1 ≤ (2 : ℝ) ^ e - 1 :=
      sub_le_sub_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hbe) _
    exact mul_le_mul_of_nonneg_left
      (_root_.add_le_add (le_refl (24 : ℝ))
        (div_le_div_of_nonneg_left (by norm_num) hden hde)) hCbox
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ Cbox * (Q.size : ℝ) ^ (1 + e) := hbox Q hsafe
      _ ≤ Cbox * (n : ℝ) ^ (1 + e) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hsize) (by linarith)) hCbox
      _ ≤ _ := mul_le_mul_of_nonneg_right hCtarget (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · intro j hj
    have hshell := IntRect.regionalEntropy_shell_le_of_safe_box
      Λ q D₀ Ω hΩ A Q hsafe j L (Nat.log 2 L) hj hL
      (Nat.pow_log_le_self 2 (by omega))
      (Nat.lt_pow_succ_log_self (b := 2) (by decide) L) hbudget e Cbox he hCbox hbox
    have hprefix : positiveDepthPrefix A
        (fun x ↦ ambientDepth Q.toFinset hQ x.val) (j : ℤ) =
        A.filter fun x ↦ x.val ∈ (Q.dilate j).toFinset \ Q.toFinset := by
      rw [positiveDepthPrefix_eq_filter_ambientDilation]
      simp only [Int.toNat_natCast, ← Q.toFinset_dilate]
    rw [hprefix]
    calc
      _ ≤ Cbox * (24 + 64 / ((2 : ℝ) ^ e - 1)) * (Q.size : ℝ) * (L : ℝ) ^ e := hshell
      _ ≤ Cbox * Cshell * (n : ℝ) * (L : ℝ) ^ e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff (Nat.cast_le.mpr hsize) (Nat.cast_nonneg _) (by positivity))
          (Real.rpow_nonneg (Nat.cast_nonneg L) e)
      _ ≤ Cbox * (Cshell + 1) * ((n : ℝ) * (L : ℝ) ^ e + n) := by
        nlinarith [mul_nonneg hCbox (show 0 ≤ (n : ℝ) * (L : ℝ) ^ e by positivity),
          mul_nonneg (mul_nonneg hCbox (by positivity : 0 ≤ Cshell + 1)) (Nat.cast_nonneg n)]

/-- One coefficient before all current exponents and physical rectangles
supplies the exact original-state target/prefix inputs of the rough scanner.
Source: `08-scanner.tex`, lines 705--729. -/
theorem exists_weakRectangle_source_entropy_bounds
    (b Cbox : ℝ) (hb : 0 < b) (hCbox : 0 ≤ Cbox) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : StateSpace Λ q), ‖Ω‖ = 1 →
      ∀ (A : Finset (Site Λ)) (Q : IntRect) (hQ : Q.toFinset.Nonempty),
        IsSafe Λ A D₀ Q → ∀ n L : ℕ, Q.size ≤ n → 1 ≤ L → L ≤ Q.size →
        D₀ * L + L ≤ D₀ * Q.size →
        ∀ e : ℝ, b ≤ e →
        (∀ Q' : IntRect, IsSafe Λ A D₀ Q' →
          regionalEntropy Λ q Ω (rectRegion A Q') ≤ Cbox * (Q'.size : ℝ) ^ (1 + e)) →
        regionalEntropy Λ q Ω (rectRegion A Q) ≤ Ce * (n : ℝ) ^ (1 + e) ∧
          ∀ j : ℕ, j ≤ L →
            regionalEntropy Λ q Ω
              (positiveDepthPrefix A (fun x ↦ ambientDepth Q.toFinset hQ x.val) (j : ℤ)) ≤
                Ce * ((n : ℝ) * (L : ℝ) ^ e + n) :=
  ⟨_, weakRectangleSourceEntropyCoefficient_nonneg hb hCbox,
    weakRectangle_source_entropy_bounds b Cbox hb hCbox⟩

end TNLean.PEPS.AreaLaw.Scan
