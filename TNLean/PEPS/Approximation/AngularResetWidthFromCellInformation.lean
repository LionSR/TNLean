/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularResetWidth

/-!
# Reset widths from a bounded number of cell contributions

A fixed logarithmic lower scale makes the information reset width smaller than
one third of the available annular width. Both constants are chosen before the
system size and scale.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 745–778,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.Approximation

/-- A uniform cell cost and a fixed bound on the number of cells admit one
logarithmic lower scale for every subsequent reset. The cell-count bound is
allowed to be real and nonnegative, and the logarithmic exponent may be zero.

Source: polynomial-PEPS manuscript, equation `eq:info-reset-scale-cost` and
its ensuing constant choice, `02-information.tex`, lines 745–778. -/
theorem exists_angular_reset_width_lt_of_cell_information
    (a' d Cp C₁ N K p : ℝ) (ha' : 0 < a') (hd : 0 < d) (hd1 : d ≤ 1)
    (hCp : 0 < Cp) (hC₁ : 0 < C₁) (hN : 0 ≤ N) (hK : 0 ≤ K) (hp : 0 < p) :
    ∃ D L₀ : ℝ, 1 ≤ D ∧ Real.exp 1 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ s : ℝ, D * Real.log L ≤ s →
        1 ≤ d * s ∧
          Cp * (1 + L ^ (-p) + N * C₁ * (1 + Real.log (d * s)) ^ K + Real.log L) <
            a' * s / 3 := by
  let D := max 1 (max (4 * Cp / (a' / 3)) (1 / d))
  obtain ⟨L₁, hL₁, hbound⟩ := exists_angular_reset_width_lt_of_slope
    K (Cp * (2 + N * C₁)) Cp (a' / 3) D (by positivity)
      (zero_lt_one.trans_le (le_max_left _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨D, max L₁ (Real.exp 1), le_max_left _ _, le_max_right _ _,
    fun L hL s hs ↦ ?_⟩
  have hlog : 1 ≤ Real.log L :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le
      ((le_max_right _ _).trans hL))).2 ((le_max_right _ _).trans hL)
  have hDs : D ≤ s :=
    (le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _)) hlog).trans hs
  have hds : 1 ≤ d * s := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp
      (((le_max_right _ _).trans (le_max_right _ _)).trans hDs : 1 / d ≤ s)
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hDs
  have hsmall : L ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [hL₁.trans ((le_max_left _ _).trans hL)]) (by linarith)
  have hpoly : (1 + Real.log (d * s)) ^ K ≤ (1 + Real.log s) ^ K :=
    Real.rpow_le_rpow (by linarith [Real.log_nonneg hds])
      (add_le_add (le_refl 1) (Real.log_le_log (zero_lt_one.trans_le hds)
        (by nlinarith [hs1] : d * s ≤ s))) hK
  have hone : 1 ≤ (1 + Real.log s) ^ K :=
    Real.one_le_rpow (by linarith [Real.log_nonneg hs1]) hK
  have hcost :
      Cp * (1 + L ^ (-p) + N * C₁ * (1 + Real.log (d * s)) ^ K + Real.log L) ≤
        Cp * (2 + N * C₁) * (1 + Real.log s) ^ K + Cp * Real.log L := by
    have hweighted := mul_le_mul_of_nonneg_left hpoly (mul_nonneg hN hC₁.le)
    have hinner : 1 + L ^ (-p) + N * C₁ * (1 + Real.log (d * s)) ^ K +
        Real.log L ≤ (2 + N * C₁) * (1 + Real.log s) ^ K + Real.log L := by
      nlinarith only [hsmall, hone, hweighted]
    nlinarith only [mul_le_mul_of_nonneg_left hinner hCp.le]
  exact ⟨hds, by
    simpa only [div_mul_eq_mul_div] using
      hbound L ((le_max_left _ _).trans hL) s hs _ hcost⟩

end TNLean.PEPS.Approximation
