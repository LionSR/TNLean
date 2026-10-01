/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary matrices preserve inner products of Euclidean vectors

A unitary complex matrix `U` preserves the dot products `star x ⬝ᵥ y` of coordinate vectors.
Consequently, for Euclidean vectors `x`, `y`, the images `U x` and `U y` have the same inner
product, and `U x` has the norm of `x`. The images are given as Euclidean vectors `x'`, `y'`
whose coordinate functions are `U *ᵥ x` and `U *ᵥ y`.

## Main results

* `Matrix.star_mulVec_dotProduct_mulVec_of_mem_unitary`: `star (U x) ⬝ᵥ U y = star x ⬝ᵥ y`.
* `Matrix.inner_eq_of_mulVec_eq`: `⟨U x|U y⟩ = ⟨x|y⟩`.
* `Matrix.norm_eq_of_mulVec_eq`: `‖U x‖ = ‖x‖`.
-/

open scoped InnerProductSpace

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ}

/-- A unitary matrix preserves the dot products `star x ⬝ᵥ y`. -/
theorem star_mulVec_dotProduct_mulVec_of_mem_unitary (hU : U ∈ unitary (Matrix ι ι ℂ))
    (x y : ι → ℂ) : star (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = star x ⬝ᵥ y := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
    Unitary.star_mul_self_of_mem hU, one_mulVec]

/-- A unitary matrix preserves the inner product of the vectors it maps. -/
theorem inner_eq_of_mulVec_eq (hU : U ∈ unitary (Matrix ι ι ℂ))
    {x y x' y' : EuclideanSpace ℂ ι}
    (hx : (fun i => x' i) = U *ᵥ fun i => x i) (hy : (fun i => y' i) = U *ᵥ fun i => y i) :
    ⟪x', y'⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (fun i => y' i) ⬝ᵥ star (fun i => x' i) = (fun i => y i) ⬝ᵥ star (fun i => x i)
  rw [hx, hy, dotProduct_comm, dotProduct_comm _ (star _),
    star_mulVec_dotProduct_mulVec_of_mem_unitary hU]

/-- A unitary matrix preserves the norm of the vector it maps. -/
theorem norm_eq_of_mulVec_eq (hU : U ∈ unitary (Matrix ι ι ℂ)) {x x' : EuclideanSpace ℂ ι}
    (hx : (fun i => x' i) = U *ᵥ fun i => x i) : ‖x'‖ = ‖x‖ := by
  have h := inner_eq_of_mulVec_eq hU hx hx
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖x'‖ ^ 2 = ‖x‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'

end Matrix
