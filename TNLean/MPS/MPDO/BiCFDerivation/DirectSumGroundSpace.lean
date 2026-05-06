/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.BiCFDerivation.DirectSumInput
import TNLean.MPS.ParentHamiltonian.BlockStrip

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

/-- Under block injectivity, the finite-chain image space has dimension equal to
the boundary matrix algebra. -/
theorem groundSpace_finrank_eq_of_isNBlkInjective {A : MPSTensor d D}
    (hA : IsNBlkInjective A L) :
    Module.finrank ℂ (groundSpace A L) = D ^ 2 := by
  rw [groundSpace, LinearMap.finrank_range_of_inj
    (groundSpaceMap_injective_of_isNBlkInjective hA)]
  calc
    Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ)
        = (Fintype.card (Fin D) * Fintype.card (Fin D)) * Module.finrank ℂ ℂ := by
            simpa using (Module.finrank_matrix ℂ ℂ (Fin D) (Fin D))
    _ = D * D := by simp
    _ = D ^ 2 := by simp [pow_two]

/-- Equal finite-chain image spaces for two block-injective tensors force equal
bond dimensions. -/
theorem bondDim_eq_of_groundSpace_eq_of_isNBlkInjective
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hG : groundSpace A L = groundSpace B L) :
    D₁ = D₂ := by
  have hfinA := groundSpace_finrank_eq_of_isNBlkInjective (A := A) hA
  have hfinB := groundSpace_finrank_eq_of_isNBlkInjective (A := B) hB
  have hsq : D₁ ^ 2 = D₂ ^ 2 := by
    calc
      D₁ ^ 2 = Module.finrank ℂ (groundSpace A L) := hfinA.symm
      _ = Module.finrank ℂ (groundSpace B L) := by rw [hG]
      _ = D₂ ^ 2 := hfinB
  exact Nat.mul_self_inj.mp (by simpa [pow_two] using hsq)

/-- The paper's dimension step for the two-block direct-sum argument.

If the finite-chain image space of the larger block is contained in that of the
smaller block, and both blocks are length-`L` block-injective, then their bond
dimensions are equal and the image spaces are equal. -/
theorem bondDim_eq_and_groundSpace_eq_of_groundSpace_le_of_isNBlkInjective_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hD : D₂ ≤ D₁) (hLe : groundSpace A L ≤ groundSpace B L) :
    D₁ = D₂ ∧ groundSpace A L = groundSpace B L := by
  have hfinLe := Submodule.finrank_mono hLe
  have hfinA := groundSpace_finrank_eq_of_isNBlkInjective (A := A) hA
  have hfinB := groundSpace_finrank_eq_of_isNBlkInjective (A := B) hB
  have hsq_le : D₁ ^ 2 ≤ D₂ ^ 2 := by
    simpa [hfinA, hfinB] using hfinLe
  have hsq_ge : D₂ ^ 2 ≤ D₁ ^ 2 := Nat.pow_le_pow_left hD 2
  have hsq : D₁ ^ 2 = D₂ ^ 2 := le_antisymm hsq_le hsq_ge
  have hD_eq : D₁ = D₂ := Nat.mul_self_inj.mp (by simpa [pow_two] using hsq)
  have hfinEq :
      Module.finrank ℂ (groundSpace A L) = Module.finrank ℂ (groundSpace B L) := by
    simpa [hfinA, hfinB] using hsq
  exact ⟨hD_eq, Submodule.eq_of_le_of_finrank_eq hLe hfinEq⟩

/-- The three-block trace relation plus the paper's size ordering gives equality
of finite-chain image spaces in the two-block direct-sum argument. -/
theorem bondDim_eq_and_groundSpace_eq_of_three_block_trace_relation_left_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    {ΔA : Matrix (Fin D₁) (Fin D₁) ℂ}
    {ΔB : Matrix (Fin D₂) (Fin D₂) ℂ}
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hD : D₂ ≤ D₁) (hΔA : ΔA ≠ 0)
    (hRel : ∀ w : Fin (L + (L + L)) → Fin d,
      Matrix.trace (ΔA * evalWord A (List.ofFn w)) +
        Matrix.trace (ΔB * evalWord B (List.ofFn w)) = 0) :
    D₁ = D₂ ∧ groundSpace A L = groundSpace B L := by
  exact bondDim_eq_and_groundSpace_eq_of_groundSpace_le_of_isNBlkInjective_of_dim_ge
    hA hB hD (groundSpace_le_of_three_block_trace_relation_left hA hΔA hRel)

end MPSTensor
