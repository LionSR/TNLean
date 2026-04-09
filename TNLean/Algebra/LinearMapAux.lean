/- 
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Data.Complex.Basic

/-!
# Auxiliary linear-map lemmas

General-purpose linear-map lemmas that are not specific to any chapter's
theory.

## Main results

- `LinearMap.ne_zero_of_eigenvector`: a nonzero eigenvector for a nonzero
  eigenvalue forces a linear map to be nonzero
- `ne_zero_of_pos_eigenvector`: a positive-eigenvalue equation with nonzero
  eigenvector forces a linear map to be nonzero
-/

/-- A nonzero eigenvector for a nonzero eigenvalue forces a linear map to be nonzero. -/
theorem LinearMap.ne_zero_of_eigenvector
    {R M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] [NoZeroSMulDivisors R M]
    {E : M →ₗ[R] M} {ρ : M} {μ : R}
    (hρ_ne : ρ ≠ 0) (hμ_ne : μ ≠ 0) (hEig : E ρ = μ • ρ) :
    E ≠ 0 := by
  intro hE0
  have hρ_zero : μ • ρ = 0 := by
    simpa [hE0] using hEig.symm
  exact hρ_ne ((eq_zero_or_eq_zero_of_smul_eq_zero hρ_zero).resolve_left hμ_ne)

/-- A positive-eigenvalue equation with nonzero eigenvector forces a linear map to be nonzero. -/
theorem ne_zero_of_pos_eigenvector
    {M : Type*}
    [AddCommMonoid M] [Module ℂ M] [NoZeroSMulDivisors ℂ M]
    {E : M →ₗ[ℂ] M} {ρ : M} {r : ℝ}
    (hρ_ne : ρ ≠ 0) (hr : 0 < r) (hEig : E ρ = (r : ℂ) • ρ) :
    E ≠ 0 := by
  exact LinearMap.ne_zero_of_eigenvector hρ_ne (by exact_mod_cast hr.ne') hEig
