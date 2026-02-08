import MPSLean.MPS.Defs

import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Simplicity and Skolem–Noether for matrix algebras

This file provides the "abstract algebra" ingredients for the Fundamental Theorem of MPS:

* **Simplicity** (`linear_mul_endomorphism_bijective`): A nonzero multiplicative linear
  endomorphism of a matrix algebra is bijective, because the kernel is a two-sided ideal
  in a simple ring.
* **Skolem–Noether** (`skolemNoether_matrix`): Every algebra automorphism of `Matrix n n ℂ`
  is inner (conjugation by an invertible matrix).
* **`linearMapToAlgHom`**: Promotes a multiplicative surjective linear map to an algebra
  homomorphism (proving `T 1 = 1`).
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- Lemma 5 (paper proof sketch, now proved):

A nonzero multiplicative `ℂ`-linear endomorphism of `D×D` matrices is bijective.

*Proof idea:* Multiplicativity makes `T` a (non-unital) ring endomorphism; its kernel is a two-sided
ideal, so by simplicity of the matrix ring it is either `⊥` or `⊤`. The latter would force
`T = 0`, hence the kernel is `⊥` and `T` is injective; finite-dimensionality upgrades injective to
surjective.
-/
theorem linear_mul_endomorphism_bijective
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hMul : ∀ M N, T (M * N) = T M * T N)
    (hNonzero : T ≠ 0) : Function.Bijective T := by
  classical
  cases D with
  | zero =>
      -- The `0×0` matrix algebra is a subsingleton, so any endomorphism is bijective.
      simpa using
        (Function.bijective_of_subsingleton
          (f := (T : Matrix (Fin 0) (Fin 0) ℂ → Matrix (Fin 0) (Fin 0) ℂ)))
  | succ D' =>
      -- Package `T` as a non-unital ring hom.
      let f :
          Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ →ₙ+*
            Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ :=
        { toFun := T
          map_zero' := by simp
          map_add' := by intro A B; simp [T.map_add A B]
          map_mul' := hMul }
      -- The kernel is either `⊥` or `⊤`; `⊤` would force `T = 0`.
      have hker : TwoSidedIdeal.ker f = ⊥ := by
        rcases (eq_bot_or_eq_top (TwoSidedIdeal.ker f)) with h | h
        · exact h
        · exact absurd (LinearMap.ext fun A => by
            simpa [f] using (TwoSidedIdeal.mem_ker (f := f)).1
              (by simp [h] : A ∈ TwoSidedIdeal.ker f)) hNonzero
      exact ⟨by simpa [f] using (TwoSidedIdeal.ker_eq_bot (f := f)).1 hker,
             LinearMap.surjective_of_injective (by simpa [f] using
               (TwoSidedIdeal.ker_eq_bot (f := f)).1 hker)⟩

/-- Lemma 6 (Skolem–Noether for matrices, *proved*): any `ℂ`-algebra automorphism of
`Matrix n n ℂ` is inner.

We use the Mathlib theorem `AlgEquiv.eq_linearEquivConjAlgEquiv` on endomorphism algebras, and the
canonical algebra equivalence `Matrix.toLinAlgEquiv'`. -/
theorem skolemNoether_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (f : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) :
    ∃ X : GL n ℂ, ∀ M : Matrix n n ℂ,
      f M = (X : Matrix n n ℂ) * M * ((X⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
  classical
  -- Transport `f` to an automorphism of endomorphisms of `n → ℂ`.
  let e : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ) := Matrix.toLinAlgEquiv'
  let fEnd : Module.End ℂ (n → ℂ) ≃ₐ[ℂ] Module.End ℂ (n → ℂ) := e.symm.trans (f.trans e)
  obtain ⟨T, hT⟩ := AlgEquiv.eq_linearEquivConjAlgEquiv (f := fEnd)
  -- Turn the linear equivalence `T` into an invertible matrix `X`.
  let X : GL n ℂ :=
    (Matrix.GeneralLinearGroup.toLin (n := n) (R := ℂ)).symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv T)
  refine ⟨X, ?_⟩
  intro M
  -- We show equality after applying the algebra equivalence `e : Matrix ≃ₐ End`, and then use
  -- injectivity.
  apply e.injective
  -- First rewrite `e (f M)` using the definition of `fEnd`.
  have hfEnd : fEnd (e M) = e (f M) := by
    -- `fEnd` is defined as `e.symm ≫ f ≫ e`.
    simp [fEnd]
  -- Next rewrite `fEnd` as conjugation by `T`.
  have hconj : fEnd (e M) = (T.conjAlgEquiv ℂ) (e M) := by
    -- `hT : fEnd = T.conjAlgEquiv ℂ`.
    exact congrArg (fun g => g (e M)) hT
  -- Identify `e X` with the underlying linear map of `T`.
  have hX_toLin :
      Matrix.GeneralLinearGroup.toLin X =
        LinearMap.GeneralLinearGroup.ofLinearEquiv T := by
    -- By construction of `X`.
    simp [X]
  have hX_lin : e (X : Matrix n n ℂ) = (T : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
    -- `toLin` is `Units.mapEquiv` of `e.toMulEquiv`.
    -- We extract the underlying map on units and then coerce to linear maps.
    --
    -- The key simp lemma is `Units.coe_mapEquiv`.
    have := congrArg (fun u : LinearMap.GeneralLinearGroup ℂ (n → ℂ) =>
      (↑u : (n → ℂ) →ₗ[ℂ] n → ℂ)) hX_toLin
    -- Unfold `Matrix.GeneralLinearGroup.toLin`.
    --
    -- `simp` turns `toLin` into `Units.mapEquiv`, and then `Units.coe_mapEquiv` gives the coercion
    -- to endomorphisms.
    simpa [Matrix.GeneralLinearGroup.toLin, Units.coe_mapEquiv, e] using this
  have hX_lin_inv :
      e ((X⁻¹ : GL n ℂ) : Matrix n n ℂ) = (T.symm : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
    -- First identify the inverse in the general linear groups.
    have hX_toLin_inv :
        Matrix.GeneralLinearGroup.toLin (X⁻¹) =
          LinearMap.GeneralLinearGroup.ofLinearEquiv T.symm := by
      calc
        Matrix.GeneralLinearGroup.toLin (X⁻¹)
            = (Matrix.GeneralLinearGroup.toLin X)⁻¹ := by
                simp [MulEquiv.map_inv]
        _   = (LinearMap.GeneralLinearGroup.ofLinearEquiv T)⁻¹ := by
                simp [hX_toLin]
        _   = LinearMap.GeneralLinearGroup.ofLinearEquiv T.symm := by
                exact (LinearMap.GeneralLinearGroup.ofLinearEquiv_inv (f := T)).symm
    -- Now coerce to linear maps.
    have := congrArg (fun u : LinearMap.GeneralLinearGroup ℂ (n → ℂ) =>
      (↑u : (n → ℂ) →ₗ[ℂ] n → ℂ)) hX_toLin_inv
    -- `toLin` unfolds to `Units.mapEquiv e.toMulEquiv`; coercing a unit gives `e` applied to the
    -- matrix coercion; the `Units.val_inv_eq_inv_val` / `map_inv` dance is handled by `simp`.
    simp only [Matrix.GeneralLinearGroup.toLin, Units.coe_mapEquiv, e] at this ⊢
    convert this using 1
  -- Now compute both sides under `e`.
  -- Left: `e (f M)`
  -- Right: `e (X * M * X⁻¹)`
  -- Use multiplicativity of `e` and the `conjAlgEquiv` formula.
  calc
    e (f M)
        = fEnd (e M) := by simp [hfEnd]
    _   = (T.conjAlgEquiv ℂ) (e M) := by simp [hconj]
    _   = (T : (n → ℂ) →ₗ[ℂ] n → ℂ) ∘ₗ e M ∘ₗ (T.symm : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
          -- `conjAlgEquiv` is `x ↦ T ∘ x ∘ T⁻¹`.
          simp [LinearEquiv.conjAlgEquiv_apply]
    _   = e (X : Matrix n n ℂ) * e M * e ((X⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
          -- Turn compositions into multiplication in `Module.End` and rewrite using `hX_lin`.
          -- (Multiplication in `Module.End` is composition.)
          rw [← hX_lin, ← hX_lin_inv]
          simp [Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _   = e ((X : Matrix n n ℂ) * M * ((X⁻¹ : GL n ℂ) : Matrix n n ℂ)) := by
          -- Use multiplicativity of `e`.
          simp [mul_assoc]

/-- Build an `ℂ`-algebra homomorphism from a multiplicative `ℂ`-linear map.

The only nontrivial field is `map_one'`, which follows from surjectivity: if `T` is surjective, then
`T 1` acts as a two-sided identity on the codomain, hence must equal `1`. -/
noncomputable def linearMapToAlgHom
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hMul : ∀ M N, T (M * N) = T M * T N)
    (hSurj : Function.Surjective T) :
    Matrix (Fin D) (Fin D) ℂ →ₐ[ℂ] Matrix (Fin D) (Fin D) ℂ := by
  classical
  -- First prove `T 1 = 1`.
  have hOne : T (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    rcases hSurj (1 : Matrix (Fin D) (Fin D) ℂ) with ⟨x, hx⟩
    have : (1 : Matrix (Fin D) (Fin D) ℂ) = T 1 := by
      calc (1 : Matrix (Fin D) (Fin D) ℂ)
          = T x := hx.symm
        _ = T (x * 1) := by rw [mul_one]
        _ = T x * T 1 := hMul x 1
        _ = 1 * T 1 := by rw [hx]
        _ = T 1 := one_mul _
    exact this.symm
  -- Now package as an algebra hom.
  refine
    { toRingHom :=
        { toFun := T
          map_one' := hOne
          map_mul' := hMul
          map_zero' := by simp
          map_add' := by intro M N; simp [T.map_add M N] }
      commutes' := ?_ }
  intro c
  -- `algebraMap` is `c • 1`, and `T` is `ℂ`-linear.
  simp [Algebra.algebraMap_eq_smul_one, hOne]

end MPSTensor
