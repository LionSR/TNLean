/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Periodic Z-gauge construction

This file contains the standalone Z-gauge matrix constructions used in the
periodic equal-case fundamental theorem of arXiv:1708.00029. The declarations
are separated from the non-periodic fundamental theorem theory to isolate the
Section 3–Section 4 periodic constructions.
-/

open scoped Matrix

namespace MPSTensor

/-- Entrywise ratio used in the periodic Z-gauge construction. -/
noncomputable def zGaugeEntry (μ ν : ℂ) : ℂ := μ / ν

/-- If `μ^m = ν^m` and `ν ≠ 0`, then `(μ/ν)^m = 1`. -/
theorem zGaugeEntry_pow_eq_one_of_pow_eq
    {m : ℕ} {μ ν : ℂ} (hpow : μ ^ m = ν ^ m) (hν : ν ≠ 0) :
    (zGaugeEntry μ ν) ^ m = 1 := by
  simp only [zGaugeEntry, div_pow, hpow, div_self (pow_ne_zero m hν)]

/-- The ratio defining the Z-gauge rescales `ν` back to `μ`. -/
theorem zGaugeEntry_mul_right {μ ν : ℂ} (hν : ν ≠ 0) :
    zGaugeEntry μ ν * ν = μ := by
  unfold zGaugeEntry
  exact div_mul_cancel₀ μ hν

section ZGaugeDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Diagonal matrix implementing the periodic Z-gauge from a matched list of weights. -/
noncomputable def zGaugeDiagonal (μ ν : n → ℂ) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => zGaugeEntry (μ i) (ν i))

/-- If matched weights have equal `m`-th powers and the denominator weights are nonzero, then
the associated Z-gauge diagonal satisfies `Z^m = 1`. -/
theorem zGaugeDiagonal_pow_eq_one
    (m : ℕ) (μ ν : n → ℂ)
    (hpow : ∀ i, μ i ^ m = ν i ^ m)
    (hν : ∀ i, ν i ≠ 0) :
    zGaugeDiagonal (n := n) μ ν ^ m = 1 := by
  simp only [zGaugeDiagonal, Matrix.diagonal_pow, Pi.pow_def]
  congr 1; ext i
  exact zGaugeEntry_pow_eq_one_of_pow_eq (hpow i) (hν i)

/-- Pointwise form of `Z * diag(ν) = diag(μ)` for the periodic Z-gauge. -/
theorem zGaugeDiagonal_mul_diagonal
    (μ ν : n → ℂ)
    (hν : ∀ i, ν i ≠ 0) :
    zGaugeDiagonal (n := n) μ ν * Matrix.diagonal ν = Matrix.diagonal μ := by
  simp only [zGaugeDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  exact zGaugeEntry_mul_right (hν i)

end ZGaugeDiagonal

end MPSTensor
