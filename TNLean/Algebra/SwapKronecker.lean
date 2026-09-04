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
`𝕊(A ⊗ B) = (B ⊗ A)𝕊`. The source states the equivalent two-sided identity at
arXiv:1703.09188, `paper_v2.tex` lines 1316--1319, and later uses it in the
gauge-invariance argument at lines 1624--1630. The one-sided forms below are
proved entrywise.

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
  arXiv:1703.09188, lines 1316--1319, 1608--1610, and
  1624--1630][Cirac2017MPU]
-/

open scoped Kronecker

namespace Matrix

variable {n : ℕ}

/-- The tensor-factor exchange intertwines the two orders of a Kronecker
product: `𝕊(A ⊗ B) = (B ⊗ A)𝕊`.

This is one side of the exchange identity in arXiv:1703.09188,
`paper_v2.tex` lines 1316--1319, and is the algebraic step behind the gauge
invariance asserted at lines 1624--1630. -/
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

The general identity gives `tr[𝕊(x ⊗ x†)] = n`. In the MPU application,
`x` acts on a space of dimension `d²`, giving the value `d²` in
arXiv:1703.09188, `paper_v2.tex` lines 1608--1610. -/
theorem trace_swapMatrix_mul_of_eq_smul_kronecker_conjTranspose
    {M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} {x : Matrix (Fin n) (Fin n) ℂ}
    (σ : ℂ) (hx : x ∈ unitaryGroup (Fin n) ℂ) (hM : M = σ • (x ⊗ₖ xᴴ)) :
    (swapMatrix n * M).trace = σ * n := by
  rw [hM, Matrix.mul_smul, Matrix.trace_smul,
    trace_swapMatrix_mul_kronecker_conjTranspose_of_mem_unitaryGroup x hx, smul_eq_mul]

end Matrix
