/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Basis

/-!
# The isometry which restores representation multiplicities on a bond

For a multiplicity space of dimension \(m>0\), the map
\(X\mapsto m^{-1/2}X\otimes I_m\) preserves the Hilbert–Schmidt inner product.
Applied independently to the irreducible blocks, it is the bond isometry in the
semi-regular bond-dimension reduction of Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Section 7, `Papers/1001.3807/paper_v3.tex`, lines 2992–3019.
The source takes \(m_i=d_i\), the multiplicity of the \(i\)-th irreducible
representation in the regular representation.

This module proves the stated bond isometry and its action on representation
matrices. The identification of its product over lattice bonds with a complete
PEPS contraction is a separate assertion.
-/

open scoped Matrix Kronecker

namespace TNLean.PEPS

variable {ι μ : Type*} [DecidableEq μ] [Fintype μ]

/-- Restore a multiplicity space by adjoining its normalized identity matrix.
Source: SCP10, Section 7, lines 3008–3019; the source takes its dimension equal
to the dimension of the corresponding irreducible representation. -/
noncomputable def multiplicityBondMap : Matrix ι ι ℂ →ₗ[ℂ] Matrix (ι × μ) (ι × μ) ℂ :=
  (Real.sqrt (Fintype.card μ : ℝ) : ℂ)⁻¹ •
    (Matrix.kroneckerBilinear (R := ℂ)).flip (1 : Matrix μ μ ℂ)

/-- The bond map adjoins the identity on the multiplicity factor. -/
@[simp]
theorem multiplicityBondMap_apply (X : Matrix ι ι ℂ) :
    multiplicityBondMap (μ := μ) X =
      (Real.sqrt (Fintype.card μ : ℝ) : ℂ)⁻¹ • (X ⊗ₖ (1 : Matrix μ μ ℂ)) := rfl

variable [DecidableEq ι]

/-- A matrix unit is sent to the normalized sum over equal multiplicity indices.
This is the explicit basis map of SCP10, Section 7, lines 3008–3019. -/
theorem multiplicityBondMap_single (a b : ι) :
    multiplicityBondMap (μ := μ) (Matrix.single a b 1) =
      (Real.sqrt (Fintype.card μ : ℝ) : ℂ)⁻¹ •
        ∑ c : μ, Matrix.single (a, c) (b, c) 1 := by
  ext ⟨i, c⟩ ⟨j, d⟩
  simp [multiplicityBondMap_apply, Matrix.single_apply, Matrix.one_apply,
    Matrix.sum_apply, Prod.mk.injEq]
  done

omit [DecidableEq ι] in
/-- The multiplicity-restoring bond map preserves the Hilbert–Schmidt inner product.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem trace_multiplicityBondMap_conjTranspose_mul [Fintype ι] [Nonempty μ] (X Y : Matrix ι ι ℂ) :
    Matrix.trace ((multiplicityBondMap (μ := μ) X).conjTranspose *
      multiplicityBondMap (μ := μ) Y) = Matrix.trace (X.conjTranspose * Y) := by
  simp only [multiplicityBondMap_apply, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.trace_smul, Matrix.trace_kronecker, Matrix.trace_one,
    star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg _),
    mul_left_comm, Complex.ofReal_natCast,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), mul_one]

end TNLean.PEPS
