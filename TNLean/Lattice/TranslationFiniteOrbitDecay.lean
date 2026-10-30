/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.PowerExponential

/-!
# Exponential decay after rounding a finite-orbit spacing

Let `L = N / (2(m+1))` be the integer orbit spacing. Exponential decay at
distance `L/2` gives decay in the physical size `N` at the positive rate
`γ/(4(m+1))`; rounding costs only the prefactor `exp(γ/2)`.
Fixed support offsets cost `exp(γ(2ρ+2))`. A common near/far estimate retains
the coefficient `2^m-1` and includes every small size, even `L=0`.

These are scalar bounds used in the finite-dimensional translation argument
for Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1644–1654.
They impose no bound on coordinate denominators.
-/

namespace TNLean.Lattice

/-- Rounding the orbit spacing loses at most one half after division by two.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem translation_half_natDiv_lower_bound (N m : ℕ) :
    (N : ℝ) / (4 * ((m : ℝ) + 1)) ≤
      ((N / (2 * (m + 1)) : ℕ) : ℝ) / 2 + 1 / 2 := by
  have hd : 0 < 2 * (m + 1) := by omega
  have hmod := Nat.mod_lt N hd
  have hrepr := Nat.mod_add_div N (2 * (m + 1))
  have hnat : N ≤ (2 * (m + 1)) * (N / (2 * (m + 1)) + 1) := by nlinarith
  have hreal : (N : ℝ) ≤ (2 * ((m : ℝ) + 1)) *
      (((N / (2 * (m + 1)) : ℕ) : ℝ) + 1) := by exact_mod_cast hnat
  apply (div_le_iff₀ (show (0 : ℝ) < 4 * ((m : ℝ) + 1) by positivity)).mpr
  nlinarith

/-- Exponential decay at half the integer orbit spacing gives decay in system size.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem exp_neg_half_translation_natDiv_le (N m : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    Real.exp (-(γ * (((N / (2 * (m + 1)) : ℕ) : ℝ) / 2))) ≤
      Real.exp (γ / 2) * Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * N)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := mul_le_mul_of_nonneg_left (translation_half_natDiv_lower_bound N m) hγ
  have hs' : (γ / (4 * ((m : ℝ) + 1))) * N ≤
      γ * (((N / (2 * (m + 1)) : ℕ) : ℝ) / 2) + γ / 2 := by
    calc _ = γ * ((N : ℝ) / (4 * ((m : ℝ) + 1))) := by ring
      _ ≤ γ * (((N / (2 * (m + 1)) : ℕ) : ℝ) / 2 + 1 / 2) := hs
      _ = _ := by ring
  linarith


/-- The size-decay rate is strictly positive whenever the spatial rate is positive.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem translation_finiteOrbit_rate_pos (m : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    0 < γ / (4 * ((m : ℝ) + 1)) := div_pos hγ (by positivity)

/-- Fixed support offsets are absorbed into a size-independent prefactor.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem translation_exp_floor_decay_le (N m : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) (ρ : ℝ) :
    Real.exp (-(γ * (((N / (2 * (m + 1)) : ℕ) : ℝ) / 2 - 2 * ρ - 1))) ≤
      Real.exp (γ * (2 * ρ + 2)) * Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * N)) := by
  have he := exp_neg_half_translation_natDiv_le N m hγ
  calc Real.exp (-(γ * (((N / (2 * (m + 1)) : ℕ) : ℝ) / 2 - 2 * ρ - 1)))
      = Real.exp (γ * (2 * ρ + 1)) *
          Real.exp (-(γ * (((N / (2 * (m + 1)) : ℕ) : ℝ) / 2))) := by
            rw [← Real.exp_add]
            congr 1
            ring
    _ ≤ Real.exp (γ * (2 * ρ + 1)) *
        (Real.exp (γ / 2) * Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * N))) :=
      mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ = Real.exp (γ * (2 * ρ + 1) + γ / 2) *
        Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * N)) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (γ * (2 * ρ + 2)) *
        Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * N)) := by
          gcongr
          nlinarith

/-- The finite-orbit coefficient absorbs a unit coefficient for positive orbit dimension.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem one_le_two_pow_sub_one (m : ℕ) (hm : 1 ≤ m) : 1 ≤ (2 : ℝ) ^ m - 1 := by
  have hp : 1 ≤ (2 : ℝ) ^ (m - 1) := one_le_pow₀ (by norm_num)
  have heq : (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [heq]
  linarith

/-- Near sizes, including zero orbit spacing, are absorbed by the same explicit
prefactor as the far-distance estimate, with coefficient `2^m-1`.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem translation_finiteOrbit_decay_of_near_far (N m : ℕ) (hm : 1 ≤ m)
    {γ ρ C z : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C) (htriv : z ≤ C)
    (hfar : 2 * ρ + 1 < ((N / (2 * (m + 1)) : ℕ) : ℝ) / 2 →
      z ≤ ((2 : ℝ) ^ m - 1) * C *
        Real.exp (-(γ * (((N / (2 * (m + 1)) : ℕ) : ℝ) / 2 - 2 * ρ - 1)))) :
    z ≤ ((2 : ℝ) ^ m - 1) * C * Real.exp (γ * (2 * ρ + 2)) *
      Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * N)) := by
  have hc := one_le_two_pow_sub_one m hm
  have hc0 : 0 ≤ ((2 : ℝ) ^ m - 1) * C := mul_nonneg (by linarith) hC
  by_cases hnear : ((N / (2 * (m + 1)) : ℕ) : ℝ) / 2 ≤ 2 * ρ + 1
  · have hratio : (N : ℝ) / (4 * ((m : ℝ) + 1)) ≤ 2 * ρ + 2 := by
      linarith [translation_half_natDiv_lower_bound N m]
    have hscaled := mul_le_mul_of_nonneg_left hratio hγ.le
    have heq : γ * ((N : ℝ) / (4 * ((m : ℝ) + 1))) =
        (γ / (4 * ((m : ℝ) + 1))) * N := by ring
    rw [heq] at hscaled
    have he : 1 ≤ Real.exp (γ * (2 * ρ + 2)) *
        Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * N)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      linarith
    calc z ≤ C := htriv
      _ ≤ ((2 : ℝ) ^ m - 1) * C := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc hC
      _ ≤ (((2 : ℝ) ^ m - 1) * C) *
          (Real.exp (γ * (2 * ρ + 2)) *
            Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * N))) :=
        le_mul_of_one_le_right hc0 he
      _ = _ := by ring
  · have hh := hfar (lt_of_not_ge hnear)
    have he := translation_exp_floor_decay_le N m hγ.le ρ
    exact hh.trans ((mul_le_mul_of_nonneg_left he hc0).trans_eq (by ring))

end TNLean.Lattice
