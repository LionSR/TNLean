/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basis

/-!
# Scalar commutant lemma: center of M_n(R) = R·1

If a matrix `Z` commutes with every element of a spanning set of `M_n(R)`,
then `Z` is a scalar matrix. This is the algebraic fact that the center
of the full matrix algebra over a commutative ring is trivial.

## Main results

* `Matrix.commute_span_top_isScalar`: if `Z` commutes with a spanning set,
  then `Z = scalar n c` for some `c`.
-/

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
  {R : Type*} [CommSemiring R]

/-- A matrix that commutes with a spanning set of `M_n(R)` lies in the center,
hence is a scalar matrix. -/
theorem commute_span_top_isScalar
    (Z : Matrix n n R)
    {S : Set (Matrix n n R)}
    (hS : Submodule.span R S = ⊤)
    (hZ : ∀ M ∈ S, Z * M = M * Z) :
    ∃ c : R, Z = Matrix.scalar n c := by
  have hcomm_all : ∀ M : Matrix n n R, Z * M = M * Z := by
    intro M
    have hM : M ∈ Submodule.span R S := hS ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx => exact hZ x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
    | smul r x _ hx =>
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hx]
  have hcenter : Z ∈ Set.center (Matrix n n R) := by
    rw [Set.mem_center_iff]
    exact {
      comm := fun a => show Z * a = a * Z from hcomm_all a
      left_assoc := fun b c => (mul_assoc Z b c).symm
      right_assoc := fun a b => mul_assoc a b Z
    }
  rw [center_eq_scalar_image] at hcenter
  obtain ⟨c, _, rfl⟩ := hcenter
  exact ⟨c, rfl⟩

end Matrix
