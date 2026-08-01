/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SkolemNoetherUnitary
import TNLean.Channel.Schwarz.PositiveMapProperties

/-!
# Positive automorphisms of complex matrix algebras

A positive algebra automorphism of a nonzero full complex matrix algebra
preserves adjoints and is therefore a star-algebra automorphism.  Unitary
Skolem--Noether then realizes it as conjugation by a unitary matrix.

## Main results

* `exists_unitary_conj_of_positive_algEquiv_matrix`
* `exists_unitary_conj_of_positive_bijective_multiplicative_matrix_linearMap`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 1955--1997
* [Wolf--Perez-Garcia 2010] arXiv:1005.4545, Theorem 8
-/

open scoped Matrix

namespace MPSTensor

/-- A positive algebra automorphism of a nonzero full complex matrix algebra
is implemented by unitary conjugation.

The positivity assumption is imposed on the underlying linear map.  It gives
adjoint preservation, after which unitary Skolem--Noether applies.

Source: CPSV16, arXiv:1606.00608, Appendix C.4, lines 1955--1997, together
with Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8. -/
theorem exists_unitary_conj_of_positive_algEquiv_matrix
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)
    (hf : IsPositiveMap f.toLinearMap) :
    ∃ U : Matrix.unitaryGroup n ℂ, ∀ M : Matrix n n ℂ,
      f M = (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)ᴴ := by
  let fstar : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
    StarAlgEquiv.ofAlgEquiv f fun M ↦ by
      rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
      exact hf.map_conjTranspose M
  exact exists_unitary_conj_of_starAlgEquiv_matrix fstar

/-- A positive, bijective, multiplicative linear endomorphism of a
nonzero full complex matrix algebra is implemented by unitary conjugation.

This form permits applications in which the algebra equivalence has first
been constructed as a linear extension.

Source: CPSV16, arXiv:1606.00608, Appendix C.4, lines 1955--1997, together
with Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8. -/
theorem exists_unitary_conj_of_positive_bijective_multiplicative_matrix_linearMap
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hMul : ∀ A B, T (A * B) = T A * T B)
    (hBij : Function.Bijective T)
    (hPos : IsPositiveMap T) :
    ∃ U : Matrix.unitaryGroup n ℂ, ∀ M : Matrix n n ℂ,
      T M = (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)ᴴ := by
  obtain ⟨X, hX⟩ := hBij.2 1
  have hOne : T 1 = 1 := by
    calc
      T 1 = 1 * T 1 := (one_mul _).symm
      _ = T X * T 1 := by rw [hX]
      _ = T (X * 1) := (hMul X 1).symm
      _ = 1 := by rw [mul_one, hX]
  let f : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ :=
    AlgEquiv.ofBijective
      { toFun := T
        map_one' := hOne
        map_mul' := hMul
        map_zero' := T.map_zero
        map_add' := T.map_add
        commutes' := fun c ↦ by
          rw [Algebra.algebraMap_eq_smul_one, T.map_smul, hOne] }
      hBij
  have hfPos : IsPositiveMap f.toLinearMap := by
    intro M hM
    exact hPos M hM
  obtain ⟨U, hU⟩ := exists_unitary_conj_of_positive_algEquiv_matrix f hfPos
  exact ⟨U, hU⟩

end MPSTensor
