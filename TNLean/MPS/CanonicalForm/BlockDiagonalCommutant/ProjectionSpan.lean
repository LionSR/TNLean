/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Provides `Matrix.blockProjection`, `Matrix.IsBlockDiagonal'`, and the
-- projection-commutant criterion used below.
import Mathlib.Data.Complex.Basic
import TNLean.Algebra.ScalarCommutant

/-!
# Projection-span lemmas for block-diagonal commutants

This module contains the algebraic span facts used to turn commutation with a
family of generators into block diagonality with respect to dependent
direct-sum sectors.
-/

open scoped Matrix BigOperators

namespace Matrix

variable {ι α : Type*} {n : ι → Type*}

section CommutesSpan

variable [Fintype ι] [DecidableEq ι]
variable [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]

/-- If every block projection lies in the span of a matrix family `S`, then any
matrix commuting with all members of `S` is block diagonal.

This is the common linearity step used in commutant arguments: commutation
extends from generators to their span, giving commutation with each projection;
`Matrix.isBlockDiagonal'_of_commutes_blockProjection` then kills all off-block
entries. -/
theorem isBlockDiagonal'_of_commutes_span_blockProjection
    {S : α → Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ}
    {X : Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ}
    (hProj : ∀ k : ι,
      blockProjection (n := n) (R := ℂ) k ∈ Submodule.span ℂ (Set.range S))
    (hComm : ∀ a : α, X * S a = S a * X) :
    IsBlockDiagonal' X := by
  classical
  apply isBlockDiagonal'_of_commutes_blockProjection (n := n) (R := ℂ)
  intro k
  have hcomm_span : ∀ M ∈ Submodule.span ℂ (Set.range S), X * M = M * X := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
        rcases hM with ⟨a, rfl⟩
        exact hComm a
    | zero => simp
    | add M N _ _ hM hN => rw [mul_add, add_mul, hM, hN]
    | smul c M _ hM =>
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hM]
  exact hcomm_span (blockProjection (n := n) (R := ℂ) k) (hProj k)

end CommutesSpan

section ProjectionSpan

variable [DecidableEq ι]
variable [(i : ι) → DecidableEq (n i)]

/-- If a family of block tuples spans the full product algebra, then the span of
its nonzero componentwise scalar multiples, embedded as dependent block-diagonal
matrices, contains each sector projection.

This is the algebraic finite-span reduction used for assembled tensors: after a
finite word-tuple span theorem supplies the full product algebra
`(i : ι) → Matrix (n i) (n i) ℂ`, the diagonal embedding of those same word
tuples contains the projections onto the individual direct-sum sectors. -/
theorem blockProjection_mem_span_blockDiagonal'_of_pi_span_eq_top
    {T : α → (i : ι) → Matrix (n i) (n i) ℂ} {c : ι → ℂ}
    (hc : ∀ i : ι, c i ≠ 0)
    (hSpan : Submodule.span ℂ (Set.range T) =
      (⊤ : Submodule ℂ ((i : ι) → Matrix (n i) (n i) ℂ)))
    (k : ι) :
    blockProjection (n := n) (R := ℂ) k ∈
      Submodule.span ℂ (Set.range fun a : α =>
        Matrix.blockDiagonal' fun i : ι => c i • T a i) := by
  classical
  let target : (i : ι) → Matrix (n i) (n i) ℂ :=
    fun i => if i = k then (c i)⁻¹ • 1 else 0
  let L : ((i : ι) → Matrix (n i) (n i) ℂ) →ₗ[ℂ]
      Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ := {
    toFun := fun M => Matrix.blockDiagonal' fun i : ι => c i • M i
    map_add' := by
      intro M N
      ext x y
      rcases x with ⟨i, p⟩
      rcases y with ⟨j, q⟩
      by_cases hij : i = j
      · subst j
        simp [Pi.add_apply, smul_add]
      · simp [Matrix.blockDiagonal'_apply_ne _ p q hij]
    map_smul' := by
      intro a M
      ext x y
      rcases x with ⟨i, p⟩
      rcases y with ⟨j, q⟩
      by_cases hij : i = j
      · subst j
        simp [smul_smul, mul_comm, mul_left_comm]
      · simp [Matrix.blockDiagonal'_apply_ne _ p q hij] }
  have htarget : target ∈ Submodule.span ℂ (Set.range T) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hmap_span : ∀ M ∈ Submodule.span ℂ (Set.range T),
      L M ∈ Submodule.span ℂ (Set.range fun a : α =>
        Matrix.blockDiagonal' fun i : ι => c i • T a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
        rcases hM with ⟨a, rfl⟩
        exact Submodule.subset_span ⟨a, rfl⟩
    | zero =>
        have hL0 : L 0 = 0 := by
          ext x y
          rcases x with ⟨i, p⟩
          rcases y with ⟨j, q⟩
          by_cases hij : i = j
          · subst j
            simp [L]
          · simp [L, Matrix.blockDiagonal'_apply_ne _ p q hij]
        rw [hL0]
        exact Submodule.zero_mem _
    | add M N _ _ hM hN => simpa [L.map_add] using Submodule.add_mem _ hM hN
    | smul a M _ hM => simpa [L.map_smul] using Submodule.smul_mem _ a hM
  have hL_target : L target = blockProjection (n := n) (R := ℂ) k := by
    ext x y
    rcases x with ⟨i, p⟩
    rcases y with ⟨j, q⟩
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp [L, target, blockProjection, hc i]
      · simp [L, target, blockProjection, hik]
    · simp [L, blockProjection, Matrix.blockDiagonal'_apply_ne _ p q hij]
  simpa [L, hL_target] using hmap_span target htarget

end ProjectionSpan

end Matrix
