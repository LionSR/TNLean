/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Homogeneous rounded scales and uniform shell coefficients

The rounded sublinear scale obeys a homogeneous power bound. Its shell
coefficient is uniform when the current entropy exponent lies between a positive
lower bound and a fixed upper bound. The enlargement constant and the auxiliary
power exponents may be zero in these numerical statements.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, the collar scales, lines 32–41; the fixed bootstrap parameters,
lines 693–703; and the shell input to Proposition 9.5, lines 705–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are auxiliary numerical estimates, independently formalized from the
manuscript. They supply no physical pointwise entropy input or exponent improvement.
-/

namespace TNLean.PEPS.AreaLaw

/-- Powers of the rounded sublinear scale obey an explicit homogeneous bound.
Auxiliary to the rounded collar in `08-scanner.tex`, lines 32–41 and 705–729,
at the manuscript revision stated above. -/
theorem floor_rpow_ceil_mul_rpow_le {C₂ η e : ℝ} (hC₂ : 0 ≤ C₂)
    (hη : 0 ≤ η) (he : 0 ≤ e) (s : ℕ) (hs : 1 ≤ s) :
    (Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) : ℝ) ^ e ≤
      (C₂ + 1) ^ (η * e) * (s : ℝ) ^ (η * e) := by
  have hs₁ : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hceil : (Nat.ceil (C₂ * (s : ℝ)) : ℝ) ≤ (C₂ + 1) * (s : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (mul_nonneg hC₂ (Nat.cast_nonneg s))
    nlinarith
  have hfloor : (Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) : ℝ) ≤
      ((C₂ + 1) * (s : ℝ)) ^ η :=
    (Nat.floor_le (by positivity)).trans
      (Real.rpow_le_rpow (by positivity) hceil hη)
  calc
    _ ≤ (((C₂ + 1) * (s : ℝ)) ^ η) ^ e :=
      Real.rpow_le_rpow (by positivity) hfloor he
    _ = ((C₂ + 1) * (s : ℝ)) ^ (η * e) :=
      (Real.rpow_mul (by positivity) η e).symm
    _ = _ := Real.mul_rpow (by positivity) (by positivity)

namespace Scan

/-- The rounded-shell coefficient is uniformly bounded for an exponent between
one positive lower bound and one fixed upper bound.
Source: auxiliary to `08-scanner.tex`, lines 693–703 and 717–729. -/
theorem rounded_shell_coefficient_uniform_le {b e e₀ η C₂ : ℝ}
    (hb : 0 < b) (hbe : b ≤ e) (hee₀ : e ≤ e₀)
    (hη : 0 ≤ η) (hC₂ : 0 ≤ C₂) :
    (24 + 64 / ((2 : ℝ) ^ e - 1)) * (C₂ + 1) ^ (η * e) ≤
      (24 + 64 / ((2 : ℝ) ^ b - 1)) * (C₂ + 1) ^ (η * e₀) := by
  have hdenb : 0 < (2 : ℝ) ^ b - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) hb)
  have hden : (2 : ℝ) ^ b - 1 ≤ (2 : ℝ) ^ e - 1 :=
    sub_le_sub_right (Real.rpow_le_rpow_of_exponent_le (by norm_num) hbe) 1
  have hdene : 0 < (2 : ℝ) ^ e - 1 := hdenb.trans_le hden
  have hcoeff : 24 + 64 / ((2 : ℝ) ^ e - 1) ≤
      24 + 64 / ((2 : ℝ) ^ b - 1) :=
    add_le_add_left (div_le_div_of_nonneg_left (by norm_num) hdenb hden) 24
  have hcoeff_nonneg : 0 ≤ 24 + 64 / ((2 : ℝ) ^ e - 1) :=
    add_nonneg (by norm_num) (div_nonneg (by norm_num) hdene.le)
  have hbase : 1 ≤ C₂ + 1 := by linarith
  have hpower : (C₂ + 1) ^ (η * e) ≤ (C₂ + 1) ^ (η * e₀) :=
    Real.rpow_le_rpow_of_exponent_le hbase (mul_le_mul_of_nonneg_left hee₀ hη)
  calc
    _ ≤ (24 + 64 / ((2 : ℝ) ^ e - 1)) * (C₂ + 1) ^ (η * e₀) :=
      mul_le_mul_of_nonneg_left hpower hcoeff_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff
      (Real.rpow_nonneg (zero_le_one.trans hbase) _)

end Scan

end TNLean.PEPS.AreaLaw
