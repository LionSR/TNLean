/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Basic.Complex.Basic

/-!
# Trace-one matrices have a nonzero dimension

A square complex matrix of trace one cannot be indexed by `Fin 0`, since the trace of the
empty matrix is zero. This file records that fact as a `NeZero` instance argument, used
wherever a normalized density matrix fixes the bond dimension to be positive.

## Main declarations

* `Matrix.neZero_of_trace_eq_one`: `Tr σ = 1` for `σ : Matrix (Fin D) (Fin D) ℂ` gives
  `NeZero D`.
-/

/-- A square matrix of trace one has a nonempty index: `Tr σ = 1` forces `D ≠ 0`. -/
theorem Matrix.neZero_of_trace_eq_one {D : ℕ} {σ : Matrix (Fin D) (Fin D) ℂ}
    (h : σ.trace = 1) : NeZero D :=
  ⟨by rintro rfl; simp at h⟩
