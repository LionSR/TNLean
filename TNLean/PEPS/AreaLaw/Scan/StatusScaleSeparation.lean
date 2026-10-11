/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.RadiusAsymptotics

/-!
# Literal rounded scales for the physical status estimates

For fixed exponents 0 < κ < μ, the rounded squared-logarithmic radius is
at most D = ceil(n^κ), and 4D is at most m = floor(n^μ), eventually in n.
The inequality 8Km ≤ L follows directly from K = L / (8m), including m = 0.
The threshold is chosen after the fixed exponents and radius coefficient,
but before every physical instance. No uniform threshold over unrestricted
positive exponent gaps is asserted.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32–58, at `openai/math@adc7f124`.
-/

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

/-- The floor defining the number of bands always gives the literal collar bound. -/
theorem eight_mul_bandCount_mul_le (L m : ℕ) :
    8 * (L / (8 * m)) * m ≤ L := by
  calc
    _ = (L / (8 * m)) * (8 * m) := by ring
    _ ≤ L := Nat.div_mul_le_self L (8 * m)

/-- The source's rounded powers give the three literal scale inequalities used
by the status geometry. The fixed exponent gap controls the threshold. -/
theorem eventually_status_scale_separation {Cr ell kappa mu : ℝ}
    (hCr : 0 ≤ Cr) (hkappa : 0 < kappa) (hkm : kappa < mu) :
    ∀ᶠ n : ℕ in atTop,
      let L := ⌊(n : ℝ) ^ (1 - ell)⌋₊
      let m := ⌊(n : ℝ) ^ mu⌋₊
      let D := ⌈(n : ℝ) ^ kappa⌉₊
      let K := L / (8 * m)
      2 ≤ n ∧ roundedLogRadius Cr n ≤ D ∧ 1 ≤ D ∧
        4 * D ≤ m ∧ 8 * K * m ≤ L := by
  have hratio : ∀ᶠ n : ℕ in atTop, (8 : ℝ) ≤ (n : ℝ) ^ (mu - kappa) :=
    ((tendsto_rpow_atTop (sub_pos.mpr hkm)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 8
  filter_upwards [eventually_roundedLogRadius_le_rpow hCr hkappa,
    hratio, eventually_ge_atTop (2 : ℕ)] with n hr hratio hn
  dsimp only
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ kappa := Real.one_le_rpow hnR hkappa.le
  have hceil : (⌈(n : ℝ) ^ kappa⌉₊ : ℝ) ≤ (n : ℝ) ^ kappa + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)).le
  have hmul : (n : ℝ) ^ mu = (n : ℝ) ^ kappa * (n : ℝ) ^ (mu - kappa) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  refine ⟨hn, ?_, ?_, ?_, eight_mul_bandCount_mul_le _ _⟩
  · exact_mod_cast hr.trans (Nat.le_ceil ((n : ℝ) ^ kappa))
  · exact_mod_cast hpow.trans (Nat.le_ceil ((n : ℝ) ^ kappa))
  · apply Nat.le_floor
    push_cast
    rw [hmul]
    nlinarith [mul_le_mul_of_nonneg_left hratio (zero_le_one.trans hpow)]

/-- The exact rounded band count is positive eventually for each fixed positive
window exponent strictly below the collar exponent. No unrounded quotient is
substituted for the integer division. -/
theorem eventually_one_le_source_bandCount {ell mu : ℝ}
    (hmu : 0 < mu) (hmuL : mu < 1 - ell) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * ⌊(n : ℝ) ^ mu⌋₊) := by
  have hratio : ∀ᶠ n : ℕ in atTop, (8 : ℝ) ≤ (n : ℝ) ^ (1 - ell - mu) :=
    ((tendsto_rpow_atTop (sub_pos.mpr hmuL)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 8
  filter_upwards [hratio, eventually_ge_atTop (1 : ℕ)] with n hratio hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hm : 1 ≤ ⌊(n : ℝ) ^ mu⌋₊ :=
    Nat.le_floor (Real.one_le_rpow hnR hmu.le)
  have hband : 8 * ⌊(n : ℝ) ^ mu⌋₊ ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ := by
    apply Nat.le_floor
    push_cast
    calc
      _ ≤ 8 * (n : ℝ) ^ mu :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
          (by norm_num)
      _ ≤ (n : ℝ) ^ mu * (n : ℝ) ^ (1 - ell - mu) := by
        nlinarith [mul_le_mul_of_nonneg_left hratio
          (Real.rpow_nonneg (Nat.cast_nonneg n) mu)]
      _ = (n : ℝ) ^ (1 - ell) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
  exact Nat.div_pos hband (by omega)

end TNLean.PEPS.AreaLaw.Scan
