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

/-- The ground-space map and the trace-test map have the same values; the only
difference is the side on which the boundary matrix is written before applying
trace cyclicity. -/
theorem groundSpaceMap_eq_leftTraceWordMap {D : ℕ} (A : MPSTensor d D) (L : ℕ) :
    groundSpaceMap A L = leftTraceWordMap A L := by
  ext X t
  simpa [groundSpaceMap_apply, leftTraceWordMap_apply] using
    Matrix.trace_mul_comm (evalWord A (List.ofFn t)) X

/-- The finite-chain image space is the range of the trace-test map. -/
theorem groundSpace_eq_leftTraceWordMap_range {D : ℕ} (A : MPSTensor d D) (L : ℕ) :
    groundSpace A L = (leftTraceWordMap A L).range := by
  rw [groundSpace, groundSpaceMap_eq_leftTraceWordMap]

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
  rw [groundSpace_eq_leftTraceWordMap_range A L, groundSpace_eq_leftTraceWordMap_range B L]
  exact leftTraceWordMap_range_le_of_three_block_trace_relation_left hA hΔA hRel

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
  rw [groundSpace_eq_leftTraceWordMap_range A L, groundSpace_eq_leftTraceWordMap_range B L]
  exact leftTraceWordMap_range_eq_of_three_block_trace_relation hA hB hΔA hΔB hRel

/-- Under block injectivity, the finite-chain image space has dimension equal to
the boundary matrix algebra. -/
theorem groundSpace_finrank_eq_of_isNBlkInjective {A : MPSTensor d D}
    (hA : IsNBlkInjective A L) :
    Module.finrank ℂ (groundSpace A L) = D ^ 2 := by
  rw [groundSpace_eq_leftTraceWordMap_range]
  exact leftTraceWordMap_range_finrank_eq_of_isNBlkInjective hA

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

/-- Conditional two-block directness for the three-block image spaces.

If the source-level contradiction input says that the two blocks cannot have
both equal bond dimension and equal length-`L` image space, then their
three-block image spaces have zero intersection.  This packages the formal
part of the two-block direct-sum argument: a nonzero vector in the intersection
would give a homogeneous three-block trace relation, and the dimension step
would force the forbidden equality. -/
theorem groundSpace_inf_eq_bot_of_not_bondDim_eq_and_groundSpace_eq_of_dim_ge
    {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsNBlkInjective A L) (hB : IsNBlkInjective B L)
    (hD : D₂ ≤ D₁)
    (hNoCollapse : ¬ (D₁ = D₂ ∧ groundSpace A L = groundSpace B L)) :
    groundSpace A (L + (L + L)) ⊓ groundSpace B (L + (L + L)) = ⊥ := by
  rw [eq_bot_iff]
  intro ψ hψ
  rcases Submodule.mem_inf.mp hψ with ⟨hψA, hψB⟩
  rw [groundSpace, LinearMap.mem_range] at hψA hψB
  rcases hψA with ⟨X, hXψ⟩
  rcases hψB with ⟨Y, hYψ⟩
  by_cases hX : X = 0
  · subst hX
    simpa using hXψ.symm
  · exfalso
    apply hNoCollapse
    refine bondDim_eq_and_groundSpace_eq_of_three_block_trace_relation_left_of_dim_ge
      (ΔA := X) (ΔB := -Y)
      hA hB hD hX ?_
    intro w
    let Aw := evalWord A (List.ofFn w)
    let Bw := evalWord B (List.ofFn w)
    have hcoeff :
        Matrix.trace (Aw * X) = Matrix.trace (Bw * Y) := by
      simpa [Aw, Bw, groundSpaceMap_apply] using
        congrArg (fun f : NSiteSpace d (L + (L + L)) => f w) (hXψ.trans hYψ.symm)
    calc
      Matrix.trace (X * evalWord A (List.ofFn w)) +
          Matrix.trace ((-Y) * evalWord B (List.ofFn w))
          = Matrix.trace (Aw * X) + -Matrix.trace (Y * Bw) := by
              simp [Aw, Bw, Matrix.trace_mul_comm X Aw]
      _ = Matrix.trace (Aw * X) + -Matrix.trace (Bw * Y) := by
              rw [Matrix.trace_mul_comm Y Bw]
      _ = 0 := by simp [hcoeff]

end MPSTensor
