/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Budgets
import TNLean.PEPS.AreaLaw.Scan.BootstrapParameters
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Rounded collar clearance

For a fixed positive enlargement constant and an exponent strictly between
zero and one, the rounded collar depth at the enlarged integer scale is
eventually at most half the original side length. This supplies the scalar
clearance budget for every natural safety parameter at least one.

For the fixed bootstrap parameters, the threshold depends only on the
enlargement constant and the initial entropy exponent. It is chosen before
all side lengths and safety parameters. The collar exponent is one minus
the fixed improvement fraction, rather than the window-width exponent.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, the collar scale `scanner:scales`, `08-scanner.tex`, lines 32–41;
the fixed choice `scanner:bootstrap-parameters`, lines 693–703; and the
covering-square clearance in the proof of Proposition 9.5 (`prop:small-box`),
lines 705–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are auxiliary numerical estimates for the rectangle covering argument.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open Filter

/-- A rounded sublinear scale at `n = ⌈C₂ s⌉` is eventually at most `s / 2`.
The threshold depends only on `C₂` and `η`.
Source: the safe covering-square clearance in `08-scanner.tex`, lines 705–729;
the actual collar specializes this statement to `η = 1 - ℓ`.
The rounded scale uses a fixed exponent strictly between zero and one. -/
theorem exists_two_mul_floor_rpow_ceil_mul_le {C₂ η : ℝ}
    (hC₂ : 0 < C₂) (hη : 0 < η) (hη₁ : η < 1) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      2 * Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) ≤ s := by
  have hlarge := eventually_le_natCast_rpow (sub_pos.mpr hη₁)
    (2 * (C₂ + 1) ^ η)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  refine ⟨max N 1, fun s hs ↦ ?_⟩
  have hs₁ : 1 ≤ s := (le_max_right N 1).trans hs
  have hsN : N ≤ s := (le_max_left N 1).trans hs
  have hlargeS := hN s hsN
  have hceil : (Nat.ceil (C₂ * (s : ℝ)) : ℝ) ≤ (C₂ + 1) * (s : ℝ) := by
    have hceilLt : (Nat.ceil (C₂ * (s : ℝ)) : ℝ) < C₂ * (s : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hs₁R : (1 : ℝ) ≤ s := by exact_mod_cast hs₁
    nlinarith
  have hfloor : (Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) : ℝ) ≤
      (C₂ + 1) ^ η * (s : ℝ) ^ η := by
    calc
      _ ≤ (Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η := Nat.floor_le (by positivity)
      _ ≤ ((C₂ + 1) * (s : ℝ)) ^ η :=
        Real.rpow_le_rpow (by positivity) hceil hη.le
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hreal : (2 : ℝ) * Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) ≤ s := by
    calc
      _ ≤ 2 * ((C₂ + 1) ^ η * (s : ℝ) ^ η) :=
        mul_le_mul_of_nonneg_left hfloor (by norm_num)
      _ = (2 * (C₂ + 1) ^ η) * (s : ℝ) ^ η := by ring
      _ ≤ (s : ℝ) ^ (1 - η) * (s : ℝ) ^ η :=
        mul_le_mul_of_nonneg_right hlargeS (by positivity)
      _ = s := by rw [← Real.rpow_add hspos]; simp
  exact_mod_cast hreal

/-- Half the parent side length is sufficient for the scalar shell-clearance
budget at every safety parameter at least one.
Source: the covering-square clearance in `08-scanner.tex`, lines 723–729. -/
theorem mul_collar_add_collar_le_of_two_mul_le {D₀ L s : ℕ}
    (hD₀ : 1 ≤ D₀) (htwo : 2 * L ≤ s) :
    D₀ * L + L ≤ D₀ * s := by
  have hscaled := Nat.mul_le_mul_left D₀ htwo
  have hL : L ≤ D₀ * L := by
    simpa only [one_mul] using Nat.mul_le_mul_right L hD₀
  calc
    D₀ * L + L ≤ D₀ * L + D₀ * L := Nat.add_le_add_left hL _
    _ = D₀ * (2 * L) := by ring
    _ ≤ D₀ * s := hscaled

/-- A single threshold gives a positive fixed bootstrap collar, bounds it by
half the parent side length, and supplies clearance for every safety parameter.
The threshold depends only on `C₂` and `e₀`.
Source: `scanner:bootstrap-parameters` and the safe-box clearance argument,
`08-scanner.tex`, lines 693–729; `scanner:scales`, lines 32–41. -/
theorem exists_bootstrap_collar_clearance {C₂ e₀ : ℝ}
    (hC₂ : 0 < C₂) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ s : ℕ, N ≤ s →
      let L := Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^
        (1 - BootstrapParameters.ell e₀))
      0 < L ∧ 2 * L ≤ s ∧
        ∀ D₀ : ℕ, 1 ≤ D₀ → D₀ * L + L ≤ D₀ * s := by
  obtain ⟨_, _, hℓ, hℓ₁, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  obtain ⟨N, hN⟩ := exists_two_mul_floor_rpow_ceil_mul_le hC₂
    (sub_pos.mpr hℓ₁) (sub_lt_self 1 hℓ)
  refine ⟨max N 1, le_max_right _ _, fun s hs ↦ ?_⟩
  have hs₁ : 1 ≤ s := (le_max_right N 1).trans hs
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hceil : 0 < Nat.ceil (C₂ * (s : ℝ)) := Nat.ceil_pos.mpr (mul_pos hC₂ hspos)
  have hceil₁ : (1 : ℝ) ≤ Nat.ceil (C₂ * (s : ℝ)) := by
    exact_mod_cast (Nat.succ_le_of_lt hceil)
  have hLpos := Nat.floor_pos.mpr (Real.one_le_rpow hceil₁ (sub_pos.mpr hℓ₁).le)
  have htwo := hN s ((le_max_left N 1).trans hs)
  exact ⟨hLpos, htwo, fun D₀ hD₀ ↦
    mul_collar_add_collar_le_of_two_mul_le hD₀ htwo⟩

end TNLean.PEPS.AreaLaw.Scan
