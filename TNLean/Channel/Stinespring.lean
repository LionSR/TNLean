/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Stinespring representation theorem (Wolf Ch. 2, Thm 2.2)

This file states and proves the Stinespring dilation theorem:
every completely positive map can be written as `T*(A) = V†(A ⊗ 𝟙)V`
for an explicit isometry `V` constructed from the Kraus operators.

## Main definitions

* `stinespringV`: the Stinespring isometry `V = ∑ⱼ Kⱼ ⊗ |j⟩`, a `(D·r) × D`
  matrix satisfying `V(i, j) k = (Kⱼ)_{ik}`
* `stinespringV_apply`: coordinate formula for `stinespringV`

## Main results (Wolf Thm 2.2)

* `stinespringV_conjTranspose_mul` — `V†V = ∑ⱼ Kⱼ†Kⱼ`
* `stinespringV_isometry_iff_kraus_normalized` — `V†V = 𝟙` ↔ `∑ⱼ Kⱼ†Kⱼ = 𝟙`
* `stinespring_dual_representation` — `T*(A) = V†(A ⊗ 𝟙)V` (Heisenberg picture)
* `stinespring_schrodinger_representation` — `T(ρ) = tr_r(VρV†)` (Schrödinger picture)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Thm 2.2][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### Stinespring isometry construction -/

/-- The Stinespring isometry `V : ℂ^D → ℂ^D ⊗ ℂ^r` constructed from Kraus operators.

Concretely, `V` is a `(D·r) × D` matrix defined by `V (i, j) k = (Kⱼ)_{ik}`.
This encodes `V = ∑ⱼ Kⱼ ⊗ |j⟩`, where `|j⟩` is the `j`-th standard basis vector. -/
noncomputable def stinespringV {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin r) (Fin D) ℂ :=
  fun ⟨i, j⟩ k => K j i k

@[simp]
theorem stinespringV_apply {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (i : Fin D)
    (j : Fin r) (k : Fin D) :
    stinespringV K (i, j) k = K j i k := rfl

/-- `V†V = ∑ⱼ Kⱼ†Kⱼ` for the Stinespring isometry. -/
theorem stinespringV_conjTranspose_mul {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    (stinespringV K)ᴴ * stinespringV K =
      ∑ j : Fin r, (K j)ᴴ * K j := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, stinespringV_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

/-- **Stinespring isometry condition** (Wolf Thm 2.2):
`V†V = 𝟙` if and only if `∑ⱼ Kⱼ†Kⱼ = 𝟙`, i.e., the Kraus operators are normalized
(equivalently, the map is trace-preserving). -/
theorem stinespringV_isometry_iff_kraus_normalized {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) :
    (stinespringV K)ᴴ * stinespringV K = 1 ↔
      ∑ j : Fin r, (K j)ᴴ * K j = 1 := by
  rw [stinespringV_conjTranspose_mul]

/-! ### Stinespring representation of the dual and Schrödinger maps -/

/-- **Stinespring representation, Heisenberg picture** (Wolf Thm 2.2):

  `T*(A) = V† (A ⊗ 𝟙_r) V`

where `V` is the Stinespring isometry. This matches the Kraus form
`T*(A) = ∑ⱼ Kⱼ† A Kⱼ`.

The `A` factor appears between a conjugate-transposed and non-transposed Kraus
operator because this is the Heisenberg action (`T*` on observables), i.e. the
adjoint of the Schrödinger map used on states. -/
theorem stinespring_dual_representation {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ) (A : Matrix (Fin D) (Fin D) ℂ) :
    (stinespringV K)ᴴ *
      (kroneckerMap (· * ·) A (1 : Matrix (Fin r) (Fin r) ℂ)) *
      stinespringV K =
      ∑ j : Fin r, (K j)ᴴ * A * K j := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    stinespringV_apply, kroneckerMap_apply, Matrix.one_apply,
    Matrix.sum_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]

/-- **Stinespring representation, Schrödinger picture** (Wolf Thm 2.2):

  `T(ρ)_{ij} = ∑_k (V ρ V†)_{(i,k),(j,k)} = tr_r(V ρ V†)`

where `tr_r` denotes partial trace over the dilation space `ℂ^r`. -/
theorem stinespring_schrodinger_representation {r : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin D) :
    (∑ l : Fin r, K l * X * (K l)ᴴ) i j =
    ∑ k : Fin r,
      (stinespringV K * X * (stinespringV K)ᴴ) (i, k) (j, k) := by
  -- Conjugation trick: rewrite the adjoint-side Kraus family as `fun l => (K l)ᴴ`.
  simp only [Matrix.mul_apply, Matrix.sum_apply,
    stinespringV_apply, Matrix.conjTranspose_apply]
