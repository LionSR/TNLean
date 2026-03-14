/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

/-!
# Tensor product of a linear map with the identity

This file defines the tensor product `T ⊗ id` of a linear map
`T : M_d(ℂ) →ₗ[ℂ] M_{d'}(ℂ)` with the identity on `M_{d''}(ℂ)`,
producing a linear map on bipartite matrices.

This is the key operation for constructing the Choi matrix
`τ = (T ⊗ id)(|Ω⟩⟨Ω|)` in the Choi–Jamiolkowski isomorphism.

## Main definitions

* `Matrix.tensorMapId`: `(T ⊗ id)(X)` for a linear map `T` and bipartite
  matrix `X`

## Main results

* `Matrix.tensorMapId_apply`: elementwise formula
* `Matrix.tensorMapId_kronecker`: `(T ⊗ id)(A ⊗ B) = T(A) ⊗ B`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 2][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset BigOperators

namespace Matrix

variable {d d' d'' : ℕ}

/-- Extract the `(i₂, j₂)`-slice of a bipartite matrix:
for `X : M_{d·d''}`, the slice `X_{·,i₂,·,j₂}` is a `d × d` matrix. -/
noncomputable def bipartiteSlice
    (X : Matrix (Fin d × Fin d'') (Fin d × Fin d'') ℂ)
    (i₂ j₂ : Fin d'') : Matrix (Fin d) (Fin d) ℂ :=
  fun i₁ j₁ => X (i₁, i₂) (j₁, j₂)

/-- The tensor product of a linear map `T : M_d → M_{d'}` with the identity
on `M_{d''}`. The result acts on bipartite matrices indexed by
`(Fin d' × Fin d'')`:

  `((tensorMapId T) X) (i₁, i₂) (j₁, j₂) = (T (bipartiteSlice X i₂ j₂)) i₁ j₁`

This corresponds to applying `T` to the first tensor factor and leaving
the second factor untouched. -/
noncomputable def tensorMapId
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d × Fin d'') (Fin d × Fin d'') ℂ) :
    Matrix (Fin d' × Fin d'') (Fin d' × Fin d'') ℂ :=
  fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => (T (bipartiteSlice X i₂ j₂)) i₁ j₁

@[simp]
theorem tensorMapId_apply
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d × Fin d'') (Fin d × Fin d'') ℂ)
    (i₁ : Fin d') (i₂ : Fin d'') (j₁ : Fin d') (j₂ : Fin d'') :
    tensorMapId T X (i₁, i₂) (j₁, j₂) =
      (T (bipartiteSlice X i₂ j₂)) i₁ j₁ := rfl

@[simp]
theorem bipartiteSlice_apply
    (X : Matrix (Fin d × Fin d'') (Fin d × Fin d'') ℂ)
    (i₂ j₂ : Fin d'') (i₁ j₁ : Fin d) :
    bipartiteSlice X i₂ j₂ i₁ j₁ = X (i₁, i₂) (j₁, j₂) := rfl

/-- `tensorMapId` is linear in `X`. -/
noncomputable def tensorMapIdLM
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    Matrix (Fin d × Fin d'') (Fin d × Fin d'') ℂ →ₗ[ℂ]
    Matrix (Fin d' × Fin d'') (Fin d' × Fin d'') ℂ where
  toFun := tensorMapId T
  map_add' X Y := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [tensorMapId_apply, Matrix.add_apply]
    rw [show bipartiteSlice (X + Y) i₂ j₂ =
      bipartiteSlice X i₂ j₂ + bipartiteSlice Y i₂ j₂ from by
        ext; simp [bipartiteSlice]]
    simp [map_add]
  map_smul' c X := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [tensorMapId_apply, Matrix.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [show bipartiteSlice (c • X) i₂ j₂ =
      c • bipartiteSlice X i₂ j₂ from by
        ext; simp [bipartiteSlice, Matrix.smul_apply, smul_eq_mul]]
    simp [map_smul]

/-- The key property: `(T ⊗ id)(A ⊗ B) = T(A) ⊗ B` for Kronecker products. -/
theorem tensorMapId_kronecker
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d'') (Fin d'') ℂ) :
    tensorMapId T (kroneckerMap (· * ·) A B) =
      kroneckerMap (· * ·) (T A) B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [tensorMapId_apply, kroneckerMap_apply]
  rw [show bipartiteSlice (kroneckerMap (· * ·) A B) i₂ j₂ =
    (B i₂ j₂) • A from by
      ext a b; simp [bipartiteSlice, kroneckerMap_apply]; ring]
  simp [map_smul, Matrix.smul_apply, smul_eq_mul]
  ring

end Matrix
