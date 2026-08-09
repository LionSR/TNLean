/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Rank-one matrix sandwiches

This file records the trace formula for sandwiching a matrix between two copies
of a rank-one matrix.
-/

open scoped Matrix BigOperators
open Matrix

namespace Matrix

/-- Rank-one sandwiching is scalar multiplication by the corresponding trace. -/
theorem vecMulVec_mul_mul_vecMulVec_eq_trace_smul
    {n : Type*} [Fintype n] (ρ Φ : n → ℂ) (P : Matrix n n ℂ) :
    vecMulVec ρ Φ * P * vecMulVec ρ Φ =
      trace (P * vecMulVec ρ Φ) • vecMulVec ρ Φ := by
  classical
  have hscalar : (Φ ᵥ* P) ⬝ᵥ ρ = trace (P * vecMulVec ρ Φ) := by
    simp only [vecMul, dotProduct, trace, diag, mul_apply, vecMulVec_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, hscalar, vecMulVec_smul]

/-- A vanishing trace through a rank-one matrix gives a zero sandwich. -/
theorem vecMulVec_mul_mul_vecMulVec_eq_zero_of_trace
    {n : Type*} [Fintype n] (ρ Φ : n → ℂ) (P : Matrix n n ℂ)
    (hP : trace (P * vecMulVec ρ Φ) = 0) :
    vecMulVec ρ Φ * P * vecMulVec ρ Φ = 0 := by
  rw [vecMulVec_mul_mul_vecMulVec_eq_trace_smul, hP, zero_smul]

/-- A rank-one matrix sandwiches a matrix to zero when their mixed trace vanishes. -/
theorem rankOne_sandwich_eq_zero_of_trace
    {n : Type*} [Fintype n] (E P : Matrix n n ℂ) (ρ Φ : n → ℂ)
    (hE : E = vecMulVec ρ Φ) (htrace : trace (P * E) = 0) :
    E * P * E = 0 := by
  subst E
  exact vecMulVec_mul_mul_vecMulVec_eq_zero_of_trace ρ Φ P htrace

end Matrix
