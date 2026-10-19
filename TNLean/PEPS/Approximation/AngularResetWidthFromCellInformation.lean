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
system size and scale: the slope `angularCellResetSlope C_p a' d = max(1, 12 C_p / a', 1 / d)`
and the size threshold `angularCellResetThreshold a' d C_p C₁ N K`. Every larger slope works
with the same threshold.

Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`),
`02-information.tex`, lines 745–778,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- The slope `D = max(1, 12 C_p / a', 1 / d)` of Proposition 3.4. It satisfies
`D ≥ 4 C_p / c_*` with the available width `c_* = a' / 3`, as in the source, and also
`D ≥ 1 / d`, so that the cells of side `d s` at every scale `s ≥ D log L` have side at
least one once `log L ≥ 1`.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`, lines 743 and
751–755 (`c_* = a' / 3` and `D ≥ 4 C_4 / c_*`) and 727–728 (`d s ≥ d D log L`). -/
noncomputable def angularCellResetSlope (Cp a' d : ℝ) : ℝ :=
  max 1 (max (12 * Cp / a') (1 / d))

/-- The slope of the cell reset is at least one. -/
theorem one_le_angularCellResetSlope (Cp a' d : ℝ) : 1 ≤ angularCellResetSlope Cp a' d :=
  le_max_left _ _

/-- The size threshold of the cell reset: the larger of `e` and the threshold
`angularResetWidthThreshold K (C_p (2 + N C₁)) (a' / 3) D₀` of the uniform width estimate at
the slope `D₀ = angularCellResetSlope C_p a' d`, with the reset-cost coefficients
`C₃ = C_p (2 + N C₁)` and `C₄ = C_p`.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`, lines 744–774. -/
noncomputable def angularCellResetThreshold (a' d Cp C₁ N K : ℝ) : ℝ :=
  max (angularResetWidthThreshold K (Cp * (2 + N * C₁)) (a' / 3)
    (angularCellResetSlope Cp a' d)) (Real.exp 1)

/-- The size threshold of the cell reset is at least `e`. -/
theorem exp_one_le_angularCellResetThreshold (a' d Cp C₁ N K : ℝ) :
    Real.exp 1 ≤ angularCellResetThreshold a' d Cp C₁ N K :=
  le_max_right _ _

/-- **Reset widths from a bounded number of cell contributions, with explicit constants.**
Every slope `D ≥ angularCellResetSlope C_p a' d` and every size
`L ≥ angularCellResetThreshold a' d C_p C₁ N K` give, at every scale `s ≥ D log L`, cells of
side `d s ≥ 1` and a reset width
`C_p (1 + L^{-p} + N C₁ (1 + log (d s))^K + log L)` smaller than `a' s / 3`. The threshold
does not depend on `D`; it is the threshold at the smallest admissible slope.

Source: polynomial-PEPS manuscript, equation `eq:info-reset-scale-cost` and its ensuing
constant choice, `02-information.tex`, lines 727–728 and 743–774. -/
theorem angular_reset_width_lt_of_cell_information
    {a' d Cp C₁ N K p : ℝ} (ha' : 0 < a') (hd : 0 < d) (hd1 : d ≤ 1)
    (hCp : 0 < Cp) (hC₁ : 0 < C₁) (hN : 0 ≤ N) (hK : 0 ≤ K) (hp : 0 < p)
    {D : ℝ} (hD : angularCellResetSlope Cp a' d ≤ D) :
    ∀ L : ℝ, angularCellResetThreshold a' d Cp C₁ N K ≤ L → ∀ s : ℝ, D * Real.log L ≤ s →
      1 ≤ d * s ∧
        Cp * (1 + L ^ (-p) + N * C₁ * (1 + Real.log (d * s)) ^ K + Real.log L) <
          a' * s / 3 := by
  intro L hL s hs
  set D₀ := angularCellResetSlope Cp a' d with hD₀
  have hD₀1 : 1 ≤ D₀ := one_le_angularCellResetSlope Cp a' d
  have hCD : 4 * Cp / (a' / 3) ≤ D := by
    have h12 : 4 * Cp / (a' / 3) = 12 * Cp / a' := by
      field_simp
      ring
    rw [h12]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans hD
  have hL₁ : angularResetWidthThreshold K (Cp * (2 + N * C₁)) (a' / 3) D ≤ L :=
    (angularResetWidthThreshold_anti (zero_lt_one.trans_le hD₀1) hD).trans
      ((le_max_left _ _).trans hL)
  have hbound := angular_reset_width_lt_of_threshold_le (C₄ := Cp) (by positivity)
    (zero_lt_one.trans_le (hD₀1.trans hD)) hCD hL₁
  have hlog : 1 ≤ Real.log L :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le
      ((le_max_right _ _).trans hL))).2 ((le_max_right _ _).trans hL)
  have hDs : D ≤ s :=
    (le_mul_of_one_le_right (zero_le_one.trans (hD₀1.trans hD)) hlog).trans hs
  have hds : 1 ≤ d * s := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp
      ((((le_max_right _ _).trans (le_max_right _ _)).trans hD).trans hDs : 1 / d ≤ s)
  have hs1 : 1 ≤ s := ((hD₀1.trans hD)).trans hDs
  have hsmall : L ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [two_le_angularResetWidthThreshold K (Cp * (2 + N * C₁)) (a' / 3) D])
    (by linarith)
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
  exact ⟨hds, by simpa only [div_mul_eq_mul_div] using hbound s hs _ hcost⟩

/-- A uniform cell cost and a fixed bound on the number of cells give one
logarithmic lower scale for every subsequent reset. The cell-count bound is
allowed to be real and nonnegative, and the logarithmic exponent may be zero.
The constants are `D = angularCellResetSlope C_p a' d` and
`L₀ = angularCellResetThreshold a' d C_p C₁ N K`
(`angular_reset_width_lt_of_cell_information`).

Source: polynomial-PEPS manuscript, equation `eq:info-reset-scale-cost` and
its ensuing constant choice, `02-information.tex`, lines 745–778. -/
theorem exists_angular_reset_width_lt_of_cell_information
    (a' d Cp C₁ N K p : ℝ) (ha' : 0 < a') (hd : 0 < d) (hd1 : d ≤ 1)
    (hCp : 0 < Cp) (hC₁ : 0 < C₁) (hN : 0 ≤ N) (hK : 0 ≤ K) (hp : 0 < p) :
    ∃ D L₀ : ℝ, 1 ≤ D ∧ Real.exp 1 ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ s : ℝ, D * Real.log L ≤ s →
        1 ≤ d * s ∧
          Cp * (1 + L ^ (-p) + N * C₁ * (1 + Real.log (d * s)) ^ K + Real.log L) <
            a' * s / 3 :=
  ⟨angularCellResetSlope Cp a' d, angularCellResetThreshold a' d Cp C₁ N K,
    one_le_angularCellResetSlope Cp a' d, exp_one_le_angularCellResetThreshold a' d Cp C₁ N K,
    angular_reset_width_lt_of_cell_information ha' hd hd1 hCp hC₁ hN hK hp le_rfl⟩

end TNLean.PEPS.Approximation
