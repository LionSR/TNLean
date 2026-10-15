/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.Defs
import TNLean.PEPS.AreaLaw.Scan.SourceRoughBudgetPower

/-!
# The selected-density budget on the source interpolation interval

The endpoint budget is converted to the
source density at arbitrary scanner exponents and positive total weight.
The interval is [ε/2, ε], and the replica remainder is retained exactly.
The endpoint and transport-coefficient estimates refer to the same state
and label sequence. The total weight has no prescribed upper growth bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 9.2, `08-scanner.tex`, lines 349–397 and 480–490, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- The rounded window estimate gives the source defect density, without
any additional decay margin or a polynomial upper bound on the weight.
Source: Proposition 9.2, `scanner:density-output` and lines 480–490. -/
theorem ScannerExponents.selectedDensity_budget_le_delta
    (X : ScannerExponents) {n : ℕ} {Cscale W C₁ Cr Ct Cl B G R : ℝ}
    (hscale : ScaleFacts X n Cscale) (hW : 0 < W) (hC₁ : 0 < C₁)
    (hCr : 0 ≤ Cr) (hCt : 0 ≤ Ct)
    (hB : B ≤ Cr * W * (n : ℝ) ^ (1 + X.e))
    (hG : G ≤ Ct * Real.log (n : ℝ) ^ Cl) :
    let a := X.a W n
    let ε := X.eps n
    let c := 2 * (C₁ + 1) /
      (W * ((n * X.m n : ℕ) : ℝ) * (ε / 2))
    c * (B + ((2 * n * X.m n : ℕ) : ℝ) * G * W * a ^ (1 / 4 : ℝ) + R) ≤
      X.delta W (4 * (C₁ + 1) * (Cr + 2 * Ct) * Cscale) Cl n + c * R := by
  have hprincipal := selectedDensity_budget_le_principal
    (Nat.lt_of_lt_of_le (by decide : 0 < 2) hscale.two_le_n)
    (Nat.lt_of_lt_of_le (by decide : 0 < 1) hscale.one_le_m) hW
    (show 0 ≤ X.a W n from div_nonneg hW.le (Nat.cast_nonneg _))
    (half_pos hscale.eps_pos) hC₁ hCr hCt hB hG (R := R)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (Nat.one_le_cast.mpr (Nat.le_trans (by decide) hscale.two_le_n))
  have hsum := add_le_add hscale.pow_e_div_m_le
    (le_mul_of_one_le_left
      (mul_nonneg
        (Real.rpow_nonneg (show 0 ≤ X.a W n from div_nonneg hW.le (Nat.cast_nonneg _))
          (1 / 4 : ℝ))
        (Real.rpow_nonneg hlog Cl)) hscale.one_le_C₁)
  refine hprincipal.trans (_root_.add_le_add ?_ le_rfl)
  refine (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ 2 * (C₁ + 1) * (Cr + 2 * Ct) by positivity))
    (half_pos hscale.eps_pos).le).trans ?_
  dsimp only [ScannerExponents.delta]
  exact le_of_eq (by ring)

end TNLean.PEPS.AreaLaw.Scan
