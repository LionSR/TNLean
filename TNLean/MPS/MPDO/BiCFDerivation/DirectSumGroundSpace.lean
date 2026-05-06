/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.DirectSumInput
import TNLean.MPS.ParentHamiltonian.GroundSpace

/-!
# Direct-sum image-space consequences

This file packages the algebraic three-block trace transfer as the image-space
inclusion used in David--Perez-Garcia--Schuch--Wolf, Lemma `lem:direct-sum`.
It uses only the finite-chain image-space definitions `groundSpaceMap` and
`groundSpace`; it does not use the parent-Hamiltonian uniqueness theorem.

## References

* [David--Perez-Garcia--Schuch--Wolf 2006, Lemma `lem:direct-sum`]

## Tags

matrix product states, canonical form, direct sum, block separation
-/

open scoped Matrix

namespace MPSTensor

variable {d D₁ D₂ L : ℕ}

/-- The three-block trace relation gives inclusion of the finite-chain image
spaces \(\mathcal G_L^A\subseteq \mathcal G_L^B\).

This is the formal version of the sentence “This means that
\(\mathcal G^{A^1}_{L_0+1}\subset \mathcal G^{A^2}_{L_0+1}\)” in the
two-block part of David--Perez-Garcia--Schuch--Wolf, Lemma `lem:direct-sum`. -/
theorem groundSpace_le_of_three_block_trace_relation_left
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ΔA : Matrix (Fin D₁) (Fin D₁) ℂ}
    {ΔB : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsNBlkInjective A L) (hΔA : ΔA ≠ 0)
    (hRel : ∀ w : Fin (L + (L + L)) → Fin d,
      Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
        Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0) :
    groundSpace A L ≤ groundSpace B L := by
  rintro ψ ⟨Z, rfl⟩
  obtain ⟨W, hW⟩ :=
    exists_right_trace_test_of_three_block_trace_relation_left hA hΔA hRel Z
  refine ⟨-W, ?_⟩
  ext t
  calc
    groundSpaceMap B L (-W) t =
        Matrix.trace (evalWord B (List.ofFn t) * (-W)) := by simp
    _ = Matrix.trace ((-W) * evalWord B (List.ofFn t)) := by
        rw [Matrix.trace_mul_comm]
    _ = -Matrix.trace (W * evalWord B (List.ofFn t)) := by simp
    _ = Matrix.trace (Z * evalWord A (List.ofFn t)) := by
        simpa using neg_eq_of_add_eq_zero_left (hW t)
    _ = Matrix.trace (evalWord A (List.ofFn t) * Z) := by
        rw [Matrix.trace_mul_comm]
    _ = groundSpaceMap A L Z t := by simp

/-- If both middle test matrices are nonzero, the three-block trace relation
gives equality of the finite-chain image spaces at length `L`. -/
theorem groundSpace_eq_of_three_block_trace_relation
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ΔA : Matrix (Fin D₁) (Fin D₁) ℂ}
    {ΔB : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hΔA : ΔA ≠ 0) (hΔB : ΔB ≠ 0)
    (hRel : ∀ w : Fin (L + (L + L)) → Fin d,
      Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
        Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0) :
    groundSpace A L = groundSpace B L := by
  apply le_antisymm
  · exact groundSpace_le_of_three_block_trace_relation_left hA hΔA hRel
  · rintro ψ ⟨W, rfl⟩
    obtain ⟨Z, hZ⟩ :=
      exists_left_trace_test_of_three_block_trace_relation_right hB hΔB hRel W
    refine ⟨-Z, ?_⟩
    ext t
    calc
      groundSpaceMap A L (-Z) t =
          Matrix.trace (evalWord A (List.ofFn t) * (-Z)) := by simp
      _ = Matrix.trace ((-Z) * evalWord A (List.ofFn t)) := by
          rw [Matrix.trace_mul_comm]
      _ = -Matrix.trace (Z * evalWord A (List.ofFn t)) := by simp
      _ = Matrix.trace (W * evalWord B (List.ofFn t)) := by
          simpa using neg_eq_of_add_eq_zero_right (hZ t)
      _ = Matrix.trace (evalWord B (List.ofFn t) * W) := by
          rw [Matrix.trace_mul_comm]
      _ = groundSpaceMap B L W t := by simp

end MPSTensor
