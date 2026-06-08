/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Block-diagonal intersection identities

This file records algebraic identities used in the block-diagonal
parent-Hamiltonian intersection argument.

## References

* [Perez-Garcia--Verstraete--Wolf--Cirac 2007], Theorem 12, proof around
  \(A_b C_a=D_b A_a\) and \(E=\sum_a C_a A_a^\dagger\).
* [Cirac--Perez-Garcia--Schuch--Verstraete 2021], Section IV.C, lines
  2120--2129.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Boundary-matrix identities in the PGVWC block-diagonal intersection proof.

Assume
\[
  A_b C_a=D_b A_a
\]
for all physical indices \(a,b\), and assume the right normalization
\[
  \sum_a A_aA_a^\dagger=I.
\]
Then, with \(E=\sum_a C_aA_a^\dagger\),
\[
  D_b=A_bE,\qquad A_bC_a=A_bEA_a.
\]
-/
theorem pgvwc07_boundary_matrix_identities_of_compatibility
    (A : MPSTensor d D)
    (C Dmat : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hUnital : ∑ a : Fin d, A a * (A a)ᴴ = 1)
    (hCompat : ∀ a b : Fin d, A b * C a = Dmat b * A a) :
    (∀ b : Fin d, Dmat b = A b * (∑ a : Fin d, C a * (A a)ᴴ)) ∧
      (∀ a b : Fin d,
        A b * C a = A b * (∑ c : Fin d, C c * (A c)ᴴ) * A a) := by
  classical
  have hD : ∀ b : Fin d, Dmat b = A b * (∑ a : Fin d, C a * (A a)ᴴ) := by
    intro b
    calc
      Dmat b = Dmat b * 1 := by simp
      _ = Dmat b * (∑ a : Fin d, A a * (A a)ᴴ) := by rw [hUnital]
      _ = ∑ a : Fin d, Dmat b * (A a * (A a)ᴴ) := by
            rw [Matrix.mul_sum]
      _ = ∑ a : Fin d, (Dmat b * A a) * (A a)ᴴ := by
            exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mul_assoc]
      _ = ∑ a : Fin d, (A b * C a) * (A a)ᴴ := by
            exact Finset.sum_congr rfl fun a _ => by rw [← hCompat a b]
      _ = ∑ a : Fin d, A b * (C a * (A a)ᴴ) := by
            exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mul_assoc]
      _ = A b * (∑ a : Fin d, C a * (A a)ᴴ) := by
            rw [Matrix.mul_sum]
  refine ⟨hD, ?_⟩
  intro a b
  calc
    A b * C a = Dmat b * A a := hCompat a b
    _ = A b * (∑ c : Fin d, C c * (A c)ᴴ) * A a := by rw [hD b]

end MPSTensor
