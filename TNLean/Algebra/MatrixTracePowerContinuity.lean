/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of matrix trace powers

Finite matrix multiplication and trace are continuous in the entrywise
finite-dimensional topology.  Consequently every function
`A ↦ trace (A ^ k)` is continuous, including at `k = 0` and in dimension zero.
-/

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of a fixed natural power is a continuous function of a finite
square matrix. -/
theorem continuous_trace_pow (k : ℕ) :
    Continuous (fun A : Matrix n n ℂ => Matrix.trace (A ^ k)) :=
  (continuous_pow k).matrix_trace

/-- Trace powers preserve convergence of finite square matrices. -/
theorem Filter.Tendsto.trace_pow {α : Type*} {l : Filter α}
    {f : α → Matrix n n ℂ} {A : Matrix n n ℂ}
    (h : Filter.Tendsto f l (nhds A)) (k : ℕ) :
    Filter.Tendsto (fun x => Matrix.trace ((f x) ^ k)) l
      (nhds (Matrix.trace (A ^ k))) :=
  (continuous_trace_pow k).continuousAt.tendsto.comp h

end Matrix
