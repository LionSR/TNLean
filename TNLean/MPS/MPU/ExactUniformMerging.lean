/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.UniformSuccessAttenuation
import TNLean.Circuit.UniformPostselection
import TNLean.Circuit.ExactAmplificationBudget
import Mathlib.Tactic.Linarith

/-!
# Exact merging at inverse-integer success amplitude

Let `V` be an isometry, and let `P` be an orthogonal projection with
`Vᴴ * P * V = r⁻² • 1`, where `r` is a positive integer. One additional
binary flag attenuates the success amplitude to the angle prescribed by
`r`. At most `r` two-reflection rounds then produce the original normalized
successful map in the first flag branch, with the other branch exactly zero.

The output is a matrix equality, so it preserves every phase and applies to
arbitrary coherent inputs. The success and failure isometries and the angle
feasibility are derived, rather than assumed. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. These results establish
the finite-dimensional merging operation; the complete recursive circuit
and its gate bound are separate assertions.
-/

open QuantumCircuit

namespace MPUCircuit

/-- The additional flag amplitude needed for the prescribed exact rotation.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
noncomputable def mergingAttenuation (r : ℕ) : ℝ :=
  (r : ℝ) * Real.sin (amplificationAngle r)

/-- The chosen additional flag amplitude is positive and physically allowed.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem mergingAttenuation_pos_le_one (r : ℕ) (hr : 0 < r) :
    0 < mergingAttenuation r ∧ mergingAttenuation r ≤ 1 := by
  obtain ⟨hsin, hsin1⟩ := amplificationAngle_sin_pos_le_inv r hr
  refine ⟨mul_pos (Nat.cast_pos.mpr hr) hsin, ?_⟩
  simpa only [mergingAttenuation,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hr.ne' : (r : ℝ) ≠ 0)] using
    mul_le_mul_of_nonneg_left hsin1 (Nat.cast_nonneg r)

end MPUCircuit

open scoped Matrix

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- Normalization cancels the attenuation and leaves the original successful
map in the first flag branch.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem postselectionSuccess_attenuatedIsometry_eq_first_branch
    (V : Matrix n m ℂ) (P : Matrix n n ℂ) (r : ℕ) (hr : 0 < r) :
    postselectionSuccess (attenuatedIsometry V (MPUCircuit.mergingAttenuation r))
      (attenuatedSuccessProjection P) (Real.sin (QuantumCircuit.amplificationAngle r)) =
      fromRows ((r : ℂ) • (P * V)) (0 : Matrix n m ℂ) := by
  have hs : Real.sin (QuantumCircuit.amplificationAngle r) ≠ 0 :=
    (QuantumCircuit.amplificationAngle_sin_pos_le_inv r hr).1.ne'
  have hc : (Real.sin (QuantumCircuit.amplificationAngle r) : ℂ)⁻¹ *
      (MPUCircuit.mergingAttenuation r : ℂ) = (r : ℂ) := by
    simp only [MPUCircuit.mergingAttenuation, Complex.ofReal_mul, Complex.ofReal_natCast]
    rw [mul_comm (r : ℂ) (Real.sin (QuantumCircuit.amplificationAngle r) : ℂ),
      ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs), one_mul]
  simp only [postselectionSuccess, attenuatedIsometry, attenuatedSuccessProjection,
    fromBlocks_mul_fromRows, Matrix.zero_mul, Matrix.mul_smul, smul_zero, add_zero]
  ext (i | i) j
  all_goals simp only [Matrix.smul_apply, fromRows_apply_inl, fromRows_apply_inr,
    Matrix.zero_apply, smul_eq_mul, mul_zero, ← mul_assoc, hc]

/-- The prescribed reflection rounds recover the original normalized successful
map exactly, with the attenuation flag in its first value.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem postselectionAmplificationStep_pow_eq_first_branch
    (V : Matrix n m ℂ) (P : Matrix n n ℂ) (hV : Vᴴ * V = 1) (hP : IsStarProjection P)
    (r : ℕ) (hr : 0 < r)
    (hprob : Vᴴ * P * V = ((r : ℂ)⁻¹) ^ 2 • (1 : Matrix m m ℂ)) :
    postselectionAmplificationStep (attenuatedIsometry V (MPUCircuit.mergingAttenuation r))
        (attenuatedSuccessProjection P) ^ QuantumCircuit.amplificationRounds r *
        attenuatedIsometry V (MPUCircuit.mergingAttenuation r) =
      fromRows ((r : ℂ) • (P * V)) (0 : Matrix n m ℂ) := by
  have ht := MPUCircuit.mergingAttenuation_pos_le_one r hr
  have htsq : MPUCircuit.mergingAttenuation r ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have htp : MPUCircuit.mergingAttenuation r * (r : ℝ)⁻¹ =
      Real.sin (QuantumCircuit.amplificationAngle r) := by
    rw [MPUCircuit.mergingAttenuation,
      mul_comm (r : ℝ) (Real.sin (QuantumCircuit.amplificationAngle r)),
      mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr hr.ne' : (r : ℝ) ≠ 0)]
  have hats : (attenuatedIsometry V (MPUCircuit.mergingAttenuation r))ᴴ *
      attenuatedSuccessProjection P * attenuatedIsometry V (MPUCircuit.mergingAttenuation r) =
      (Real.sin (QuantumCircuit.amplificationAngle r) : ℂ) ^ 2 • (1 : Matrix m m ℂ) := by
    simpa only [htp] using
      attenuatedIsometry_success_gram V P (MPUCircuit.mergingAttenuation r) (r : ℝ)⁻¹
        (by simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using hprob)
  have hamp :
      postselectionAmplificationStep (attenuatedIsometry V (MPUCircuit.mergingAttenuation r))
          (attenuatedSuccessProjection P) ^ QuantumCircuit.amplificationRounds r *
          attenuatedIsometry V (MPUCircuit.mergingAttenuation r) =
        postselectionSuccess (attenuatedIsometry V (MPUCircuit.mergingAttenuation r))
          (attenuatedSuccessProjection P) (Real.sin (QuantumCircuit.amplificationAngle r)) := by
    simpa only [QuantumCircuit.amplificationAngle] using
      postselectionAmplificationStep_pow_eq_success
        (attenuatedIsometry V (MPUCircuit.mergingAttenuation r)) (attenuatedSuccessProjection P)
        (attenuatedIsometry_conjTranspose_mul_self V hV _ htsq)
        (attenuatedSuccessProjection_isStarProjection P hP)
        (QuantumCircuit.amplificationRounds r) (QuantumCircuit.amplificationRounds_pos r hr)
        (by simpa only [QuantumCircuit.amplificationAngle] using hats)
  exact hamp.trans (postselectionSuccess_attenuatedIsometry_eq_first_branch V P r hr)

/-- At most `r` reflection rounds suffice for an exact merger of uniform
success amplitude `1 / r`, with no additional angle or decomposition hypotheses.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem exists_exact_uniform_merging
    (V : Matrix n m ℂ) (P : Matrix n n ℂ) (hV : Vᴴ * V = 1) (hP : IsStarProjection P)
    (r : ℕ) (hr : 0 < r)
    (hprob : Vᴴ * P * V = ((r : ℂ)⁻¹) ^ 2 • (1 : Matrix m m ℂ)) :
    ∃ ℓ ≤ r,
      postselectionAmplificationStep (attenuatedIsometry V (MPUCircuit.mergingAttenuation r))
          (attenuatedSuccessProjection P) ^ ℓ *
          attenuatedIsometry V (MPUCircuit.mergingAttenuation r) =
        fromRows ((r : ℂ) • (P * V)) (0 : Matrix n m ℂ) := by
  exact ⟨QuantumCircuit.amplificationRounds r, QuantumCircuit.amplificationRounds_le r,
    postselectionAmplificationStep_pow_eq_first_branch V P hV hP r hr hprob⟩

end Matrix
