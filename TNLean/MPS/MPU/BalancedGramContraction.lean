/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.BalancedGramMetrics
import QICLean.Analysis.MatrixSqrt
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Contraction of balanced MPU bond metrics

The positive square roots of the determinant-balanced metrics have inverse
product equal to the square root of the bond dimension times the identity.
Consequently its vectorization has squared norm equal to the square of the
bond dimension. This is the contraction estimate in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

These finite matrix identities do not assert a complete circuit construction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace MPUCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The inverse square-root contraction for a pair of balanced bond metrics.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def balancedGramContraction (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (CFC.sqrt (dualGramMetric P))⁻¹ * (CFC.sqrt P)⁻¹

/-- Balanced metrics make the contraction a scalar identity, with scalar
equal to the square root of the bond dimension. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedGramContraction_eq {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    balancedGramContraction P =
      Real.sqrt (Fintype.card ι : ℝ) • (1 : Matrix ι ι ℂ) := by
  rw [balancedGramContraction, (dualGramMetric_posDef hP).posSemidef.inv_sqrt,
    dualGramMetric_inv hP, hP.posSemidef.sqrt_smul (Nat.cast_nonneg _),
    Matrix.smul_mul, Matrix.mul_nonsing_inv _ hP.isUnit_det_cfc_sqrt]

/-- The contraction's Gram is the dimension times the identity. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedGramContraction_gram {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    (balancedGramContraction P)ᴴ * balancedGramContraction P =
      (Fintype.card ι : ℝ) • (1 : Matrix ι ι ℂ) := by
  rw [balancedGramContraction_eq hP, Matrix.conjTranspose_smul]
  simp only [star_trivial, Matrix.conjTranspose_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.one_mul]
  rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-- The squared Hilbert--Schmidt norm of the vectorized contraction is the
square of the bond dimension. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem balancedGramContraction_vec_inner {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    star (vec (balancedGramContraction P)) ⬝ᵥ vec (balancedGramContraction P) =
      (Fintype.card ι : ℂ) ^ 2 := by
  rw [Matrix.star_vec_dotProduct_vec, balancedGramContraction_gram hP,
    Matrix.trace_smul, Matrix.trace_one]
  simp [pow_two, Complex.real_smul]

end MPUCircuit
