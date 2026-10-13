/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SharpMomentScale

/-!
# Exact rounded-scale signatures and boundary cases

These examples retain the actual integer band count, the uniform order of
quantifiers and the final source exponents. Zero weight, zero budget coefficient
and negative fixed multiples are included.
-/

set_option autoImplicit false

open Filter TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

example : (((7 : ℕ) / (8 * 1) : ℕ) : ℝ) = 0 := by norm_num

example : (((8 : ℕ) / (8 * 1) : ℕ) : ℝ) = 1 := by norm_num

example (X : ScannerExponents) (n : ℕ) : X.a 0 n = 0 := by
  simp only [ScannerExponents.a, zero_div]

example (X : ScannerExponents) {n : ℕ} {B : ℝ} (hB : 1 ≤ B) :
    ¬B ≤ 0 * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12 := by
  simpa only [zero_mul, not_le] using (zero_lt_one.trans_le hB)

example (X : ScannerExponents)
    {ω CB A c : ℝ} (hmargin : ω + (1 + X.kappa) / 2 < 1 - X.ell - X.mu)
    (hCB : 0 ≤ CB) (hA : 0 ≤ A) (hc : 0 < c) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 1 ≤ X.K n ∧
      ∀ W B : ℝ, 0 ≤ W → W ≤ (n : ℝ) ^ ω → 1 ≤ B →
        B ≤ CB * (n : ℝ) * (X.D n : ℝ) * Real.log (n : ℝ) ^ 12 →
        A * X.a W n ≤ c / Real.sqrt B :=
  X.exists_a_le_moment_radius hmargin hCB hA hc

example {CB c : ℝ} (hCB : 0 ≤ CB) (hc : 0 < c) (t : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      let L := Nat.floor ((n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ)))
      let m := Nat.floor ((n : ℝ) ^ (Exponents.scannerMu : ℝ))
      let K := L / (8 * m)
      let D := Nat.ceil ((n : ℝ) ^ (Exponents.scannerKappa : ℝ))
      let a := (n : ℝ) ^ (Exponents.scannerOmega : ℝ) / (K : ℝ)
      1 ≤ K ∧ ∀ B : ℝ, 1 ≤ B →
        B ≤ CB * (n : ℝ) * (D : ℝ) * Real.log (n : ℝ) ^ 12 →
        |t * a| ≤ c / Real.sqrt B :=
  exists_final_a_le_moment_radius hCB hc t

example (a : ℝ) (ha : 0 ≤ a) : |(-3 : ℝ) * a| = 3 * a := by
  rw [abs_mul, abs_of_nonneg ha]
  norm_num

example :
    (1 - (Exponents.scannerEll : ℝ) - (Exponents.scannerMu : ℝ)) -
        ((Exponents.scannerOmega : ℝ) + (1 + (Exponents.scannerKappa : ℝ)) / 2) =
      (499879 / 2000000 : ℝ) :=
  final_scanner_moment_margin
