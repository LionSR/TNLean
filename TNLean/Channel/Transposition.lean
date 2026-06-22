/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic

/-!
# Transposition is a positive, trace-preserving map

This file introduces the matrix transposition `θ : M_d(ℂ) → M_d(ℂ)`, `θ(A) = Aᵀ`,
as a linear map and proves that it is positive and trace preserving.

Positivity follows from the fact that transposition preserves positive
semidefiniteness: if `A = U D U†` is the spectral decomposition of a Hermitian
matrix, then `Aᵀ = Ū D Uᵀ` has the same eigenvalues `D`.  Transposition is the
paradigmatic example of a positive map which is not completely positive
(Wolf, Chapter 3, §3.1).

## Main declarations

* `transpositionMap`: matrix transposition as a `ℂ`-linear map on `M_d(ℂ)`
* `transpositionMap_isPositiveMap`: transposition is a positive map
* `transpositionMap_isTracePreservingMap`: transposition is trace preserving

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

section Transposition

variable (d : ℕ)

/-- Matrix transposition `θ(A) = Aᵀ` as a `ℂ`-linear map on `M_d(ℂ)`. -/
def transpositionMap : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.transposeLinearEquiv (Fin d) (Fin d) ℂ ℂ).toLinearMap

variable {d}

@[simp] theorem transpositionMap_apply (A : Matrix (Fin d) (Fin d) ℂ) :
    transpositionMap d A = Aᵀ := rfl

/-- Transposition is a positive map: it preserves positive semidefiniteness.

For a positive semidefinite `A`, the transpose `Aᵀ` shares the eigenvalues of
`A` (Wolf, Chapter 3, §3.1), so it is again positive semidefinite. -/
theorem transpositionMap_isPositiveMap : IsPositiveMap (transpositionMap d) :=
  fun _ hA => by simpa using hA.transpose

/-- Transposition is trace preserving: `Tr(Aᵀ) = Tr(A)`. -/
theorem transpositionMap_isTracePreservingMap : IsTracePreservingMap (transpositionMap d) :=
  fun A => by simp

end Transposition
