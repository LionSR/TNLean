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
      exact Function.bijective_of_subsingleton T
  | succ D' =>
      -- Package `T` as a non-unital ring hom.
      let f : Matrix (Fin (D' + 1)) (Fin (D' + 1)) ℂ →ₙ+*
            Matrix (Fin (D' + 1)) (Fin (D' + 1)) ℂ :=
        { toFun := T, map_zero' := by simp, map_add' := T.map_add, map_mul' := hMul }
      -- The kernel is either `⊥` or `⊤`; `⊤` would force `T = 0`.
      have hker : TwoSidedIdeal.ker f = ⊥ := by
        rcases eq_bot_or_eq_top (TwoSidedIdeal.ker f) with h | h
        · exact h
        · exact absurd (LinearMap.ext fun A => by
            simpa [f] using (TwoSidedIdeal.mem_ker (f := f)).1
              (h ▸ (show A ∈ (⊤ : TwoSidedIdeal _) by simp))) hNonzero
      have hinj : Function.Injective T := by
        simpa [f] using (TwoSidedIdeal.ker_eq_bot (f := f)).1 hker
      exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

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
  -- Identify `e X` and `e X⁻¹` with the underlying linear maps of `T` and `T.symm`.
  have hX_toLin :
      Matrix.GeneralLinearGroup.toLin X =
        LinearMap.GeneralLinearGroup.ofLinearEquiv T := by simp [X]
  have hX_lin : e (X : Matrix n n ℂ) = (T : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
    -- `toLin` is `Units.mapEquiv` of `e.toMulEquiv`.
    -- The key simp lemma is `Units.coe_mapEquiv`.
    have := congrArg (fun u : LinearMap.GeneralLinearGroup ℂ (n → ℂ) =>
      (↑u : (n → ℂ) →ₗ[ℂ] n → ℂ)) hX_toLin
    simpa [Matrix.GeneralLinearGroup.toLin, Units.coe_mapEquiv, e] using this
  have hX_lin_inv :
      e ((X⁻¹ : GL n ℂ) : Matrix n n ℂ) = (T.symm : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
    have hX_toLin_inv :
        Matrix.GeneralLinearGroup.toLin (X⁻¹) =
          LinearMap.GeneralLinearGroup.ofLinearEquiv T.symm := by
      calc Matrix.GeneralLinearGroup.toLin (X⁻¹)
            = (Matrix.GeneralLinearGroup.toLin X)⁻¹ := by simp [MulEquiv.map_inv]
        _ = (LinearMap.GeneralLinearGroup.ofLinearEquiv T)⁻¹ := by simp [hX_toLin]
        _ = LinearMap.GeneralLinearGroup.ofLinearEquiv T.symm :=
              (LinearMap.GeneralLinearGroup.ofLinearEquiv_inv (f := T)).symm
    have := congrArg (fun u : LinearMap.GeneralLinearGroup ℂ (n → ℂ) =>
      (↑u : (n → ℂ) →ₗ[ℂ] n → ℂ)) hX_toLin_inv
    -- `toLin` unfolds to `Units.mapEquiv e.toMulEquiv`; coercing a unit gives `e` applied to the
    -- matrix coercion; the `Units.val_inv_eq_inv_val` / `map_inv` dance is handled by `simp`.
    simp only [Matrix.GeneralLinearGroup.toLin, Units.coe_mapEquiv, e] at this ⊢
    convert this using 1
  -- Now compute both sides under `e`.
  calc e (f M)
        = fEnd (e M) := by simp [fEnd]
    _ = (T.conjAlgEquiv ℂ) (e M) := congrArg (· (e M)) hT
    _ = (T : (n → ℂ) →ₗ[ℂ] n → ℂ) ∘ₗ e M ∘ₗ (T.symm : (n → ℂ) →ₗ[ℂ] n → ℂ) := by
          -- `conjAlgEquiv` is `x ↦ T ∘ x ∘ T⁻¹`.
          simp [LinearEquiv.conjAlgEquiv_apply]
    _ = e (X : Matrix n n ℂ) * e M * e ((X⁻¹ : GL n ℂ) : Matrix n n ℂ) := by
          -- Turn compositions into multiplication in `Module.End` and rewrite using `hX_lin`.
          rw [← hX_lin, ← hX_lin_inv]
          simp [Module.End.mul_eq_comp, LinearMap.comp_assoc]
    _ = e ((X : Matrix n n ℂ) * M * ((X⁻¹ : GL n ℂ) : Matrix n n ℂ)) := by
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
  -- First prove `T 1 = 1`: choose `x` with `T x = 1`, then `1 = T x = T(x*1) = Tx * T1 = T1`.
  have hOne : T 1 = 1 := by
    obtain ⟨x, hx⟩ := hSurj 1
    calc (T 1 : Matrix (Fin D) (Fin D) ℂ)
        = 1 * T 1 := (one_mul _).symm
      _ = T x * T 1 := by rw [hx]
      _ = T (x * 1) := (hMul x 1).symm
      _ = T x := by rw [mul_one]
      _ = 1 := hx
  exact
    { toRingHom :=
        { toFun := T
          map_one' := hOne
          map_mul' := hMul
          map_zero' := by simp
          map_add' := T.map_add }
      commutes' := fun c => by simp [Algebra.algebraMap_eq_smul_one, hOne] }

end MPSTensor
