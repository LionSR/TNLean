/-
Copyright (c) 2026 TNLean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SkolemNoether

/-!
# Gauge extraction from multiplicative linear maps

This file packages the matrix-algebra argument that turns a nonzero multiplicative
linear endomorphism into conjugation by an invertible matrix.
-/

open scoped Matrix

namespace MPSTensor

variable {D : ℕ}

/-- A nonzero multiplicative complex-linear endomorphism of a full matrix algebra is inner.

Simplicity makes the endomorphism bijective. Its surjectivity promotes it to an algebra
homomorphism, bijectivity upgrades that homomorphism to an algebra equivalence, and
Skolem--Noether realizes the equivalence as conjugation by an invertible matrix. -/
theorem exists_inner_of_linear_mul_endomorphism
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hMul : ∀ M N, T (M * N) = T M * T N)
    (hNonzero : T ≠ 0) :
    ∃ X : GL (Fin D) ℂ, ∀ M : Matrix (Fin D) (Fin D) ℂ,
      T M = (X : Matrix (Fin D) (Fin D) ℂ) * M *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  have hBij := linear_mul_endomorphism_bijective T hMul hNonzero
  let fHom := linearMapToAlgHom T hMul hBij.surjective
  let f := AlgEquiv.ofBijective fHom hBij
  obtain ⟨X, hX⟩ := skolemNoether_matrix f
  refine ⟨X, fun M => ?_⟩
  change f M = _
  exact hX M

end MPSTensor
