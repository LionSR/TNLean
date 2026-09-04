/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.SwapTrace

/-!
# The tensor-factor exchange against Kronecker products

The gauge-invariance argument for the time-reversal sign of a matrix product
unitary moves the tensor-factor exchange `𝕊` past a Kronecker product, and then
contracts the exchange against a scalar multiple of `x ⊗ x†`. This file records
the two algebraic steps.

The exchange intertwines the two orders of a Kronecker product,
`𝕊(A ⊗ B) = (B ⊗ A)𝕊`. The source asserts the resulting gauge invariance of the
trace formula for the sign without printing a derivation, at arXiv:1703.09188,
`paper_v2.tex` lines 1624--1630; the identity below is the algebraic step that
invariance rests on, and it is proved here entrywise.

Because the exchange is available only in the square product coordinates
`(Fin n) × (Fin n)`, both Kronecker factors are square of the same size.

## Main results

- `Matrix.swapMatrix_mul_kronecker`: the exchange carries a Kronecker product to
  the product with its factors exchanged.
- `Matrix.kronecker_mul_swapMatrix`: the same identity read from the other side.
- `Matrix.trace_swapMatrix_mul_of_eq_smul_kronecker_conjTranspose`: contracting
  the exchange against a scalar multiple of `x ⊗ x†` for unitary `x` returns the
  scalar times the factor dimension.

## References

* [J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix product
  unitaries: structure, symmetries, and topological invariants*,
  arXiv:1703.09188, lines 1608--1610 and 1624--1630][Cirac2017MPU]
-/

open scoped Kronecker

namespace Matrix

variable {n : ℕ}

/-- The tensor-factor exchange intertwines the two orders of a Kronecker
product: `𝕊(A ⊗ B) = (B ⊗ A)𝕊`.

This is the algebraic step behind the gauge invariance of the trace formula for
the time-reversal sign, which arXiv:1703.09188 asserts without a printed
derivation at `paper_v2.tex` lines 1624--1630. -/
theorem swapMatrix_mul_kronecker (A B : Matrix (Fin n) (Fin n) ℂ) :
    swapMatrix n * (A ⊗ₖ B) = (B ⊗ₖ A) * swapMatrix n := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    ite_and, Finset.sum_ite_eq, mul_comm]

/-- The tensor-factor exchange read from the other side:
`(A ⊗ B)𝕊 = 𝕊(B ⊗ A)`. -/
theorem kronecker_mul_swapMatrix (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A ⊗ₖ B) * swapMatrix n = swapMatrix n * (B ⊗ₖ A) :=
  (swapMatrix_mul_kronecker B A).symm

/-- Contracting the tensor-factor exchange against a scalar multiple of
`x ⊗ x†`, for a unitary `x`, returns the scalar times the factor dimension.

This is the trace evaluation `tr[𝕊 x x†] = d²` used to extract the
time-reversal sign in arXiv:1703.09188, `paper_v2.tex` lines 1608--1610, with
the scalar supplied by the symmetry relation. -/
theorem trace_swapMatrix_mul_of_eq_smul_kronecker_conjTranspose
    {M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} {x : Matrix (Fin n) (Fin n) ℂ}
    (σ : ℂ) (hx : x ∈ unitaryGroup (Fin n) ℂ) (hM : M = σ • (x ⊗ₖ xᴴ)) :
    (swapMatrix n * M).trace = σ * n := by
  rw [hM, Matrix.mul_smul, Matrix.trace_smul,
    trace_swapMatrix_mul_kronecker_conjTranspose_of_mem_unitaryGroup x hx, smul_eq_mul]

end Matrix
