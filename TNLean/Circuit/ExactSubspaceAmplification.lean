/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exact amplification of an isometric subspace

Let `G` and `H` be orthogonal isometries with the same input space. The
isometry `sin θ • G + cos θ • H` has a uniform success amplitude in the
image of `G`. Two reflections rotate this amplitude through twice the
angle `θ`. This is the finite-dimensional amplification argument in
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5.
-/

open scoped Matrix

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Reflection across the orthogonal complement of a projection.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
def subspaceReflection (P : Matrix n n ℂ) : Matrix n n ℂ :=
  1 - (2 : ℂ) • P

/-- The isometric plane parametrized by its success angle.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
noncomputable def amplificationPlane (G H : Matrix n m ℂ) (θ : ℝ) : Matrix n m ℂ :=
  (Real.sin θ : ℂ) • G + (Real.cos θ : ℂ) • H

/-- A reflection associated to an orthogonal projection is unitary.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem subspaceReflection_mem_unitaryGroup (P : Matrix n n ℂ)
    (hP : IsStarProjection P) : subspaceReflection P ∈ unitaryGroup n ℂ := by
  convert hP.one_sub.two_mul_sub_one_mem_unitary using 1
  simp only [subspaceReflection, two_mul]
  module

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
private lemma orthogonality_symmetric (G H : Matrix n m ℂ) (hGH : Gᴴ * H = 0) :
    Hᴴ * G = 0 := by
  simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
    congrArg conjTranspose hGH

/-- The two-reflection amplification operator, with the phase chosen for positive rotation.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
noncomputable def subspaceAmplificationStep (G H : Matrix n m ℂ)
    (P : Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ :=
  -(subspaceReflection (amplificationPlane G H θ * (amplificationPlane G H θ)ᴴ) *
    subspaceReflection P)

/-- The amplification operator rotates every vector in the same isometric plane through `2θ`.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem subspaceAmplificationStep_mul_plane (G H : Matrix n m ℂ) (P : Matrix n n ℂ)
    (hG : Gᴴ * G = 1) (hH : Hᴴ * H = 1) (hGH : Gᴴ * H = 0)
    (hPG : P * G = G) (hPH : P * H = 0) (θ φ : ℝ) :
    subspaceAmplificationStep G H P θ * amplificationPlane G H φ =
      amplificationPlane G H (φ + 2 * θ) := by
  have hHG := orthogonality_symmetric G H hGH
  simp only [subspaceAmplificationStep, subspaceReflection, amplificationPlane,
    Matrix.neg_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    hG, hH, hGH, hHG, hPG, hPH, smul_zero, Matrix.mul_zero, zero_add, add_zero,
    smul_smul]
  match_scalars
  · rw [Complex.sin_add, Complex.sin_two_mul, Complex.cos_two_mul_eq_one_sub]
    ring
  · rw [Complex.cos_add, Complex.sin_two_mul, Complex.cos_two_mul]
    ring

omit [Fintype m] [DecidableEq n] in
/-- Every point in an orthogonal isometric plane is an isometry.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem amplificationPlane_conjTranspose_mul_self (G H : Matrix n m ℂ)
    (hG : Gᴴ * G = 1) (hH : Hᴴ * H = 1) (hGH : Gᴴ * H = 0) (θ : ℝ) :
      (amplificationPlane G H θ)ᴴ * amplificationPlane G H θ = 1 := by
  have hHG := orthogonality_symmetric G H hGH
  simp only [amplificationPlane, conjTranspose_add, conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hG, hH, hGH, hHG,
    smul_zero, add_zero, zero_add]
  match_scalars
  simpa only [pow_two] using Complex.sin_sq_add_cos_sq (θ : ℂ)

omit [DecidableEq n] in
/-- The image Gram matrix of an isometry is an orthogonal projection.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem isStarProjection_mul_conjTranspose_of_isometry (V : Matrix n m ℂ)
    (hV : Vᴴ * V = 1) : IsStarProjection (V * Vᴴ) := by
  rw [isStarProjection_iff']
  constructor
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]
  · simp only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- The two-reflection amplification operator is unitary on the entire output space.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem subspaceAmplificationStep_mem_unitaryGroup (G H : Matrix n m ℂ)
    (P : Matrix n n ℂ) (hG : Gᴴ * G = 1) (hH : Hᴴ * H = 1) (hGH : Gᴴ * H = 0)
    (hP : IsStarProjection P) (θ : ℝ) :
    subspaceAmplificationStep G H P θ ∈ unitaryGroup n ℂ := by
  have hprod :
      subspaceReflection (amplificationPlane G H θ * (amplificationPlane G H θ)ᴴ) *
        subspaceReflection P ∈ unitaryGroup n ℂ :=
    (unitaryGroup n ℂ).mul_mem
      (subspaceReflection_mem_unitaryGroup _
        (isStarProjection_mul_conjTranspose_of_isometry _
          (amplificationPlane_conjTranspose_mul_self G H hG hH hGH θ)))
      (subspaceReflection_mem_unitaryGroup P hP)
  simpa only [subspaceAmplificationStep, mem_unitaryGroup_iff, star_neg, neg_mul_neg] using hprod

/-- After `k` amplification steps the angle has increased by `2kθ`.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem subspaceAmplificationStep_pow_mul_plane (G H : Matrix n m ℂ) (P : Matrix n n ℂ)
    (hG : Gᴴ * G = 1) (hH : Hᴴ * H = 1) (hGH : Gᴴ * H = 0)
    (hPG : P * G = G) (hPH : P * H = 0) (θ φ : ℝ) (k : ℕ) :
    subspaceAmplificationStep G H P θ ^ k * amplificationPlane G H φ =
      amplificationPlane G H (φ + (k : ℝ) * (2 * θ)) := by
  induction k with
  | zero => simp only [pow_zero, Matrix.one_mul, Nat.cast_zero, zero_mul, add_zero]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih,
      subspaceAmplificationStep_mul_plane G H P hG hH hGH hPG hPH]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- The prescribed angle gives exact amplification after `ℓ` steps, with no residual phase.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem subspaceAmplificationStep_pow_eq_good (G H : Matrix n m ℂ) (P : Matrix n n ℂ)
    (hG : Gᴴ * G = 1) (hH : Hᴴ * H = 1) (hGH : Gᴴ * H = 0)
    (hPG : P * G = G) (hPH : P * H = 0) (ℓ : ℕ) :
    subspaceAmplificationStep G H P (Real.pi / (4 * (ℓ : ℝ) + 2)) ^ ℓ *
        amplificationPlane G H (Real.pi / (4 * (ℓ : ℝ) + 2)) = G := by
  have hden : (4 * (ℓ : ℝ) + 2) ≠ 0 := by positivity
  have hangle :
      Real.pi / (4 * (ℓ : ℝ) + 2) +
          (ℓ : ℝ) * (2 * (Real.pi / (4 * (ℓ : ℝ) + 2))) = Real.pi / 2 := by
    field_simp [hden]
    ring
  rw [subspaceAmplificationStep_pow_mul_plane G H P hG hH hGH hPG hPH, hangle]
  simp [amplificationPlane]

end Matrix
