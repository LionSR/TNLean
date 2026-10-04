/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import TNLean.Circuit.Gates.TwoLevel
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Attenuating a uniform success amplitude with one binary flag

The two-by-two rotation with first column `(t, sqrt (1 - t²))` is unitary
when `t² ≤ 1`. Applying it to a new flag gives two weighted copies of an
isometry. Success requires both the original success projection and the
first flag value. Its input Gram is multiplied by `t²`, so the uniform
success amplitude `p` becomes `t * p`.

This is the attenuation step in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The matrices here
establish normalization and the exact probability identity; the complete
recursive circuit and its resource bound are separate assertions.
-/

open scoped Matrix

namespace Matrix

/-- The real rotation preparing the attenuation flag.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def attenuationRotation (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(t : ℂ), -(Real.sqrt (1 - t ^ 2) : ℂ);
    (Real.sqrt (1 - t ^ 2) : ℂ), (t : ℂ)]

/-- The attenuation rotation is unitary on both flag values.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem attenuationRotation_mem_unitaryGroup (t : ℝ) (ht : t ^ 2 ≤ 1) :
    attenuationRotation t ∈ unitaryGroup (Fin 2) ℂ := by
  have hz : ‖(⟨t, Real.sqrt (1 - t ^ 2)⟩ : ℂ)‖ = 1 := by
    simp only [Complex.norm_def, Complex.normSq_mk,
      Real.mul_self_sqrt (sub_nonneg.mpr ht)]
    rw [← pow_two, add_sub_cancel, Real.sqrt_one]
  simpa only [attenuationRotation, QuantumCircuit.rotTwo] using
    QuantumCircuit.rotTwo_mem_unitary (z := ⟨t, Real.sqrt (1 - t ^ 2)⟩) hz

variable {m n : Type*} [Fintype n] [DecidableEq m]

/-- The two flag branches of an isometry after attenuation.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def attenuatedIsometry (V : Matrix n m ℂ) (t : ℝ) : Matrix (n ⊕ n) m ℂ :=
  fromRows ((t : ℂ) • V) ((Real.sqrt (1 - t ^ 2) : ℂ) • V)

/-- Success in the first flag branch and in the original success subspace.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def attenuatedSuccessProjection (P : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks P 0 0 0

/-- Attenuation preserves the complete input Gram of an isometry.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem attenuatedIsometry_conjTranspose_mul_self
    (V : Matrix n m ℂ) (hV : Vᴴ * V = 1) (t : ℝ) (ht : t ^ 2 ≤ 1) :
    (attenuatedIsometry V t)ᴴ * attenuatedIsometry V t = 1 := by
  simp only [attenuatedIsometry, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows, conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hV]
  match_scalars
  rw [← pow_two, ← pow_two, Complex.ofReal_sqrt_sq _ (sub_nonneg.mpr ht)]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
  ring

/-- The attenuated success test is an orthogonal projection.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem attenuatedSuccessProjection_isStarProjection
    (P : Matrix n n ℂ) (hP : IsStarProjection P) :
    IsStarProjection (attenuatedSuccessProjection P) := by
  rw [isStarProjection_iff']
  constructor
  · simp only [attenuatedSuccessProjection, fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, hP.isIdempotentElem.eq]
  · have hself : Pᴴ = P := hP.isSelfAdjoint.isHermitian.eq
    simp only [star_eq_conjTranspose, attenuatedSuccessProjection,
      fromBlocks_conjTranspose, conjTranspose_zero, hself]

/-- Attenuation multiplies the uniform success amplitude by its flag coefficient.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem attenuatedIsometry_success_gram
    (V : Matrix n m ℂ) (P : Matrix n n ℂ) (t p : ℝ)
    (hprob : Vᴴ * P * V = (p : ℂ) ^ 2 • (1 : Matrix m m ℂ)) :
    (attenuatedIsometry V t)ᴴ * attenuatedSuccessProjection P * attenuatedIsometry V t =
      ((t * p : ℝ) : ℂ) ^ 2 • (1 : Matrix m m ℂ) := by
  simp only [attenuatedIsometry, attenuatedSuccessProjection,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
    fromCols_mul_fromRows, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hprob]
  match_scalars
  ring

end Matrix
