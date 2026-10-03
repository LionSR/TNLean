/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import QICLean.Algebra.MatrixGramUnitary
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Local equivalence of pure states with a common reduced density

Coefficient matrices describe pure states across a bipartition. Dividing by
their Hilbert space norm makes equality of their reduced densities equivalent
to equality of their row Gram matrices. The finite-dimensional unitary
extension theorem then gives a unitary acting on the complementary factor.

Source: SCP10, arXiv:1001.3807, Theorem 6.7 and Corollary 6.8,
local source lines 1995–2025.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix ComplexOrder

namespace TNLean.PEPS

variable {P Q : Type*} [Fintype P] [Fintype Q]

/-- A pure-state coefficient matrix divided by its Hilbert space norm.
Source: SCP10, Theorem 6.7, lines 1995–2015. -/
noncomputable def normalizedPureCutMatrix (M : Matrix P Q ℂ) : Matrix P Q ℂ :=
  ((Real.sqrt (M * M.conjTranspose).trace.re : ℝ) : ℂ)⁻¹ • M

/-- Normalization of a coefficient matrix gives its normalized reduced density.
Source: SCP10, Corollary 6.8, lines 2017–2025. -/
theorem normalizedPureCutMatrix_mul_conjTranspose (M : Matrix P Q ℂ) :
    normalizedPureCutMatrix M * (normalizedPureCutMatrix M).conjTranspose =
      (M * M.conjTranspose).trace⁻¹ • (M * M.conjTranspose) := by
  have hp := Complex.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose M).trace_nonneg
  have hre : (((M * M.conjTranspose).trace.re : ℝ) : ℂ) =
      (M * M.conjTranspose).trace := by
    apply Complex.ext <;> simp [hp.2.symm]
  simp only [normalizedPureCutMatrix, Matrix.conjTranspose_smul, star_inv₀,
    Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Complex.ofReal_sqrt_inv_mul_self _ hp.1, hre]

/-- Equal reduced densities admit a unitary on the complementary factor after
normalization, in the physical coefficient convention `B = A * U.transpose`.
This auxiliary statement is the pure-state implication used in
SCP10, Theorem 6.7 and Corollary 6.8, lines 1995–2025. -/
theorem exists_unitary_normalizedPureCutMatrix_eq_of_reducedMatrix_eq [DecidableEq Q]
    (A B : Matrix P Q ℂ)
    (hρ : (B * B.conjTranspose).trace⁻¹ • (B * B.conjTranspose) =
      (A * A.conjTranspose).trace⁻¹ • (A * A.conjTranspose)) :
    ∃ U : Matrix.unitaryGroup Q ℂ,
      normalizedPureCutMatrix B = normalizedPureCutMatrix A * (U : Matrix Q Q ℂ).transpose := by
  classical
  have hGram : (normalizedPureCutMatrix B).conjTranspose.conjTranspose *
      (normalizedPureCutMatrix B).conjTranspose =
      (normalizedPureCutMatrix A).conjTranspose.conjTranspose *
        (normalizedPureCutMatrix A).conjTranspose := by
    simpa only [Matrix.conjTranspose_conjTranspose,
      normalizedPureCutMatrix_mul_conjTranspose] using hρ
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (normalizedPureCutMatrix B).conjTranspose (normalizedPureCutMatrix A).conjTranspose hGram
  refine ⟨⟨(U : Matrix Q Q ℂ).conjTranspose.transpose, ?_⟩, ?_⟩
  · apply Matrix.transpose_mem_unitaryGroup_iff.mpr
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem U.property
  · change normalizedPureCutMatrix B = normalizedPureCutMatrix A *
      (U : Matrix Q Q ℂ).conjTranspose.transpose.transpose
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.transpose_transpose] using congrArg Matrix.conjTranspose hU

end TNLean.PEPS
