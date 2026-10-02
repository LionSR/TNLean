/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A dimension bound for exact amplification rounds

For a bond of positive dimension `r`, choose the number of rounds as
`ceil (π * r / 4)` and the rotation angle as `π / (4 * rounds + 2)`.
There are at most `r` rounds, and the chosen positive success amplitude
is at most `1 / r`. Thus a merger of success amplitude `1 / r` can first
be attenuated to the prescribed exact-amplification angle.

These are the numerical estimates used in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. They do not assert
circuit synthesis or the construction of an attenuation gate.
-/

namespace MPUCircuit

/-- The number of exact amplification rounds chosen from the bond dimension.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def amplificationRounds (r : ℕ) : ℕ :=
  ⌈Real.pi * (r : ℝ) / 4⌉₊

/-- The angle whose prescribed number of amplification rounds reaches π/2.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def amplificationAngle (r : ℕ) : ℝ :=
  Real.pi / (4 * (amplificationRounds r : ℝ) + 2)

/-- A positive bond dimension requires a positive number of rounds.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationRounds_pos (r : ℕ) (hr : 0 < r) :
    0 < amplificationRounds r := by
  rw [amplificationRounds, Nat.ceil_pos]
  positivity

/-- The chosen number of rounds is at most the bond dimension.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationRounds_le (r : ℕ) : amplificationRounds r ≤ r := by
  rw [amplificationRounds, Nat.ceil_le]
  have h := mul_le_mul_of_nonneg_right Real.pi_le_four (Nat.cast_nonneg r : 0 ≤ (r : ℝ))
  nlinarith

/-- The exact-amplification angle is positive.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationAngle_pos (r : ℕ) : 0 < amplificationAngle r := by
  unfold amplificationAngle
  positivity

/-- For a positive bond dimension the chosen angle is strictly below π/2.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationAngle_lt_pi_div_two (r : ℕ) (hr : 0 < r) :
    amplificationAngle r < Real.pi / 2 := by
  have hround : 0 < (amplificationRounds r : ℝ) :=
    Nat.cast_pos.mpr (amplificationRounds_pos r hr)
  unfold amplificationAngle
  apply (div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith [Real.pi_pos]

/-- The chosen angle is at most the inverse bond dimension.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationAngle_le_inv (r : ℕ) (hr : 0 < r) :
    amplificationAngle r ≤ (r : ℝ)⁻¹ := by
  have hround : Real.pi * (r : ℝ) / 4 ≤ (amplificationRounds r : ℝ) :=
    Nat.le_ceil _
  have hr₀ : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
  unfold amplificationAngle
  rw [← one_div (r : ℝ)]
  apply (div_le_div_iff₀ (by positivity) hr₀).mpr
  nlinarith

/-- The chosen success amplitude is positive and at most the original merger
amplitude.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem amplificationAngle_sin_pos_le_inv (r : ℕ) (hr : 0 < r) :
    0 < Real.sin (amplificationAngle r) ∧
      Real.sin (amplificationAngle r) ≤ (r : ℝ)⁻¹ := by
  constructor
  · exact Real.sin_pos_of_pos_of_lt_pi (amplificationAngle_pos r)
      ((amplificationAngle_lt_pi_div_two r hr).trans (by linarith [Real.pi_pos]))
  · exact (Real.sin_le (amplificationAngle_pos r).le).trans
      (amplificationAngle_le_inv r hr)

end MPUCircuit
