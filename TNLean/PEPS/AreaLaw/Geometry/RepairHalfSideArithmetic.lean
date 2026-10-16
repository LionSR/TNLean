/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.SimultaneousRepair

/-!
# Integral repair half-sides

At every parent scale at least one, the exponent defining the dyadic repair
half-side is a nonnegative integer. The half-side is therefore a natural
number, viewed in the real plane. This arithmetic fact ensures that the
successive centers, corners and side midpoints preserve the translated
integer mesh.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:trim-radius`, lines 380–385,
and the arithmetic of supporting lines, lines 545–558.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Geometry

/-- A repair half-side computed from a parent scale at least one is a
natural number. Source: area-law Section 11, `geometry:trim-radius`,
lines 380–385, and the integral recursion, lines 545–551. -/
theorem exists_natCast_repairHalfSide {S : ℝ} (hS : 1 ≤ S) :
    ∃ n : ℕ, repairHalfSide S = (n : ℝ) := by
  have hf : 0 ≤ (⌊(Exponents.rho : ℝ) * Real.logb 2 S⌋ : ℤ) :=
    Int.floor_nonneg.mpr
      (mul_nonneg rho_pos_lt_one.1.le (Real.logb_nonneg one_lt_two hS))
  refine ⟨2 ^ (⌊(Exponents.rho : ℝ) * Real.logb 2 S⌋ : ℤ).toNat, ?_⟩
  simp only [repairHalfSide, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
    Int.toNat_of_nonneg hf]

end TNLean.PEPS.AreaLaw.Geometry
