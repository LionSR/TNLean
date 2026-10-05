/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Logarithmic block scales and double-logarithmic tree depth

A balanced binary tree on a block of logarithmic size has double-logarithmic height.
The constants in these bounds are independent of the chain length and requested accuracy.

## References

* arXiv:2307.01696, "Tree-RG circuit with measurements" and the block-size choice after Lemma 1.
-/

namespace MPSPreparation

/-- The depth `C (h + 1)` of trees with `2^h ≤ a X + b + 1` is at most a constant times
`log(X + 1)`, for `X ≥ log 2`. -/
theorem natCast_mul_succ_le_mul_log {C h : ℕ} {a b X : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hX : Real.log 2 ≤ X) (hh : (2 : ℝ) ^ h ≤ a * X + b + 1) :
    ((C * (h + 1) : ℕ) : ℝ) ≤ C * ((1 + Real.logb 2 (a + b + 1)) / Real.log (1 + Real.log 2) +
      1 / Real.log 2) * Real.log (X + 1) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hX0 : 0 ≤ X := hl2.le.trans hX
  have hμ : 0 < Real.log (1 + Real.log 2) := Real.log_pos (by linarith)
  have hLX : Real.log (1 + Real.log 2) ≤ Real.log (X + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpos : 0 < a * X + b + 1 := by positivity
  have hh' : (h : ℝ) ≤ Real.logb 2 (a * X + b + 1) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hpos, Real.rpow_natCast]
    exact hh
  have hmul : a * X + b + 1 ≤ (a + b + 1) * (X + 1) := by nlinarith
  have hlog : Real.logb 2 (a * X + b + 1) ≤ Real.logb 2 (a + b + 1) + Real.logb 2 (X + 1) := by
    rw [← Real.logb_mul (by positivity) (by positivity)]
    exact Real.logb_le_logb_of_le one_lt_two hpos hmul
  have hκ : 0 ≤ Real.logb 2 (a + b + 1) := Real.logb_nonneg one_lt_two (by linarith)
  set κ := 1 + Real.logb 2 (a + b + 1)
  have hκμ : κ ≤ κ / Real.log (1 + Real.log 2) * Real.log (X + 1) := by
    calc κ = κ / Real.log (1 + Real.log 2) * Real.log (1 + Real.log 2) := by field_simp
      _ ≤ κ / Real.log (1 + Real.log 2) * Real.log (X + 1) := by gcongr
  have hb2 : Real.logb 2 (X + 1) = 1 / Real.log 2 * Real.log (X + 1) := by
    rw [Real.logb]; ring
  have hsucc : (h : ℝ) + 1 ≤
      (κ / Real.log (1 + Real.log 2) + 1 / Real.log 2) * Real.log (X + 1) := by
    simp only [κ] at hκμ ⊢
    nlinarith
  push_cast
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  calc (C : ℝ) * (h + 1) ≤ C * ((κ / Real.log (1 + Real.log 2) + 1 / Real.log 2) *
        Real.log (X + 1)) := mul_le_mul_of_nonneg_left hsucc hC
    _ = _ := by ring

/-- A tree of `h + 1` coarse depths with `2^{h+2} s ≤ Y < 2^{h+3} s`, for `Y ≥ 4s`. -/
theorem exists_two_pow_le {s Y : ℕ} (hs : 0 < s) (hY : 4 * s ≤ Y) :
    ∃ h : ℕ, 2 ^ (h + 2) * s ≤ Y ∧ Y < 2 ^ (h + 1) * (4 * s) := by
  have hq : Y / (4 * s) ≠ 0 := (Nat.div_pos hY (by omega)).ne'
  refine ⟨Nat.log 2 (Y / (4 * s)), ?_, ?_⟩
  · have h1 := Nat.pow_log_le_self 2 hq
    have h2 := Nat.div_mul_le_self Y (4 * s)
    calc 2 ^ (Nat.log 2 (Y / (4 * s)) + 2) * s = 2 ^ Nat.log 2 (Y / (4 * s)) * (4 * s) := by
          rw [pow_add]; ring
      _ ≤ Y / (4 * s) * (4 * s) := Nat.mul_le_mul_right _ h1
      _ ≤ Y := h2
  · have h1 := Nat.lt_pow_succ_log_self (b := 2) one_lt_two (Y / (4 * s))
    have h2 : Y < (Y / (4 * s) + 1) * (4 * s) := by
      have := Nat.lt_div_mul_add (a := Y) (b := 4 * s) (by omega)
      linarith
    calc Y < (Y / (4 * s) + 1) * (4 * s) := h2
      _ ≤ 2 ^ (Nat.log 2 (Y / (4 * s)) + 1) * (4 * s) := Nat.mul_le_mul_right _ h1

end MPSPreparation
