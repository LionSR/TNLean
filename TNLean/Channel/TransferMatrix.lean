/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.MPS.Core.Transfer
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis

/-!
# Transfer-matrix representation of channels (Wolf §2.2)

This file defines the **transfer matrix** (matrix representation) of a linear
map `T : M_D(ℂ) → M_D(ℂ)`. Given an ordered basis `{E_{kl}}` of standard
matrix units for `M_D(ℂ)`, the transfer matrix `T̂` is the `D² × D²` matrix
whose `((i,j),(k,l))`-entry is `(T(E_{kl}))_{ij}`.

The main result is that `T̂` faithfully represents `T` in the vectorized
picture: `vec(T(ρ)) = T̂ *ᵥ vec(ρ)`, and this representation is compatible
with composition. We also relate it to the Kraus representation.

## Main definitions

* `Matrix.vecMatrix`: vectorization `M_D(ℂ) → ℂ^{D×D}`, viewing a matrix as
  a function on the product index type `Fin D × Fin D`
* `Matrix.unvecMatrix`: the inverse, rebuilding a matrix from a vector
* `transferMatrix`: the `(Fin D × Fin D) × (Fin D × Fin D)` matrix
  representing `T` in the standard-basis vectorization
* `transferMatrixLM`: `transferMatrix` as a linear map from superoperators to
  matrices on the vectorized space

## Main results

* `transferMatrix_mulVec_eq`: `T̂ *ᵥ vec(ρ) = vec(T(ρ))`
* `transferMatrix_comp`: `(S ∘ T)^ = Ŝ * T̂`
* `transferMatrix_id`: the transfer matrix of the identity is the identity
* `transferMatrix_kraus`: for a Kraus map `T(X) = ∑ᵢ Kᵢ X Kᵢ†`, the transfer
  matrix is `∑ᵢ Kᵢ ⊗ K̄ᵢ`
* `MPSTensor.transferMatrix_eq`: the MPS transfer map `E_A` has transfer
  matrix `∑ᵢ Aᵢ ⊗ Āᵢ`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §2.2][Wolf2012QChannels]
-/

open scoped Matrix BigOperators
open Matrix Finset

variable {D : ℕ}

namespace Matrix

/-! ### Vectorization of matrices -/

/-- **Vectorization**: view a `D × D` matrix as a function on the product
index type `Fin D × Fin D`. This is the column-stacking map `vec`. -/
def vecMatrix (M : Matrix (Fin D) (Fin D) ℂ) : Fin D × Fin D → ℂ :=
  fun ⟨i, j⟩ => M i j

/-- **Unvectorization**: rebuild a `D × D` matrix from a function on
`Fin D × Fin D`. -/
def unvecMatrix (v : Fin D × Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => v (i, j)

@[simp]
theorem vecMatrix_apply (M : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    vecMatrix M (i, j) = M i j := rfl

@[simp]
theorem unvecMatrix_apply (v : Fin D × Fin D → ℂ) (i j : Fin D) :
    unvecMatrix v i j = v (i, j) := rfl

@[simp]
theorem unvecMatrix_vecMatrix (M : Matrix (Fin D) (Fin D) ℂ) :
    unvecMatrix (vecMatrix M) = M := by
  ext i j; simp

@[simp]
theorem vecMatrix_unvecMatrix (v : Fin D × Fin D → ℂ) :
    vecMatrix (unvecMatrix v) = v := by
  ext ⟨i, j⟩; simp

/-- Vectorization is linear. -/
noncomputable def vecMatrixLM : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D × Fin D → ℂ) where
  toFun := vecMatrix
  map_add' _ _ := by ext ⟨i, j⟩; simp [vecMatrix, Pi.add_apply]
  map_smul' _ _ := by ext ⟨i, j⟩; simp [vecMatrix, Pi.smul_apply, smul_eq_mul]

/-- Unvectorization is linear. -/
noncomputable def unvecMatrixLM : (Fin D × Fin D → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun := unvecMatrix
  map_add' _ _ := by ext i j; simp [unvecMatrix]
  map_smul' _ _ := by ext i j; simp [unvecMatrix, smul_eq_mul]

end Matrix

/-! ### The transfer matrix -/

/-- The **transfer matrix** of a linear map `T : M_D(ℂ) → M_D(ℂ)`:

  `T̂_{(i,j),(k,l)} = (T(E_{kl}))_{ij}`

where `E_{kl} = Matrix.single k l 1` is the standard matrix unit.
This is a `(Fin D × Fin D) × (Fin D × Fin D)` matrix that represents `T`
in the vectorized picture. -/
noncomputable def transferMatrix
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun ⟨i, j⟩ ⟨k, l⟩ => (T (Matrix.single k l 1)) i j

@[simp]
theorem transferMatrix_apply
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (i j k l : Fin D) :
    transferMatrix T (i, j) (k, l) = (T (Matrix.single k l 1)) i j := rfl

private lemma sum_smul_single_eq (ρ : Matrix (Fin D) (Fin D) ℂ) :
    ρ = ∑ k : Fin D, ∑ l : Fin D, ρ k l • Matrix.single k l 1 := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ext a b
  simp [Matrix.single_apply, smul_eq_mul]

/-! ### Fundamental property: T̂ represents T in the vectorized picture -/

/-- **Key property**: the transfer matrix faithfully represents `T`:
`(T̂ *ᵥ vec(ρ))_{(i,j)} = (T(ρ))_{ij}`.

This is the defining property of the transfer-matrix representation:
vectorizing `T(ρ)` is the same as multiplying `T̂` by `vec(ρ)`. -/
theorem transferMatrix_mulVec_eq
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (ρ : Matrix (Fin D) (Fin D) ℂ) :
    transferMatrix T *ᵥ Matrix.vecMatrix ρ =
      Matrix.vecMatrix (T ρ) := by
  ext ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, transferMatrix_apply,
    Matrix.vecMatrix_apply, Fintype.sum_prod_type]
  have key : T ρ = ∑ k, ∑ l, ρ k l • T (Matrix.single k l 1) := by
    conv_lhs => rw [sum_smul_single_eq ρ]
    simp_rw [map_sum, LinearMap.map_smul]
  rw [key]
  simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-! ### Compatibility with composition -/

/-- The transfer matrix of a composition is the product of transfer matrices. -/
theorem transferMatrix_comp
    (S T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    transferMatrix (S ∘ₗ T) = transferMatrix S * transferMatrix T := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [transferMatrix_apply, LinearMap.comp_apply, Matrix.mul_apply,
    Fintype.sum_prod_type]
  have key : S (T (Matrix.single k l 1)) =
      ∑ a, ∑ b, (T (Matrix.single k l 1)) a b • S (Matrix.single a b 1) := by
    conv_lhs => rw [sum_smul_single_eq (T (Matrix.single k l 1))]
    simp_rw [map_sum, LinearMap.map_smul]
  rw [key]
  simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- The transfer matrix of the identity map is the identity matrix. -/
@[simp]
theorem transferMatrix_id :
    transferMatrix (LinearMap.id : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] _) = 1 := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [transferMatrix_apply, LinearMap.id_apply, Matrix.one_apply, Prod.mk.injEq]
  rw [Matrix.single_apply]
  simp [eq_comm]

/-- `transferMatrix` is injective: distinct linear maps have distinct
transfer matrices. -/
theorem transferMatrix_injective :
    Function.Injective
      (transferMatrix : (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] _) →
        Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := by
  intro S T h
  ext M i j
  have key := congr_fun (congr_fun (congrArg Matrix.mulVec h) (Matrix.vecMatrix M)) (i, j)
  simp only [transferMatrix_mulVec_eq, Matrix.vecMatrix_apply] at key
  exact key

/-! ### Transfer matrix as a linear map -/

/-- `transferMatrix` as a linear map from superoperators to matrices on the
vectorized space. -/
noncomputable def transferMatrixLM :
    (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) →ₗ[ℂ]
      Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ where
  toFun := transferMatrix
  map_add' S T := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [transferMatrix_apply, LinearMap.add_apply, Matrix.add_apply]
  map_smul' c T := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [transferMatrix_apply, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul]

/-! ### Kraus representation of the transfer matrix -/

/-- For a Kraus map `T(X) = ∑ᵢ Kᵢ X Kᵢ†`, the transfer matrix is
`∑ᵢ Kᵢ ⊗ K̄ᵢ` (Kronecker product of `Kᵢ` with its entrywise conjugate).

This connects the channel-theoretic Kraus representation with the
vectorized transfer-matrix picture. -/
theorem transferMatrix_kraus
    {r : ℕ} (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hK : ∀ X, T X = ∑ i : Fin r, K i * X * (K i)ᴴ) :
    transferMatrix T =
      ∑ n : Fin r,
        kroneckerMap (· * ·) (K n) ((K n).map (starRingEnd ℂ)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [transferMatrix_apply, hK, Matrix.sum_apply, kroneckerMap_apply, Matrix.map_apply,
    starRingEnd_apply]
  congr 1; ext n
  -- (K n * E_{kl} * (K n)ᴴ)_{ij} = (K n)_{ik} * star((K n)_{jl})
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
  simp only [ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-! ### Connection to MPS transfer maps -/

namespace MPSTensor

/-- The MPS transfer map `E_A(X) = ∑ᵢ Aᵢ X Aᵢ†` has transfer matrix
`∑ᵢ Aᵢ ⊗ Āᵢ`.

This bridges Wolf's channel-side §2.2 transfer matrix with the MPS-side
transfer operator. -/
theorem transferMatrix_eq (A : MPSTensor d D) :
    transferMatrix (MPSTensor.transferMap A) =
      ∑ n : Fin d,
        kroneckerMap (· * ·) (A n) ((A n).map (starRingEnd ℂ)) :=
  transferMatrix_kraus A _ (fun X => by simp [transferMap_apply])

end MPSTensor
