import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped Matrix

namespace Matrix

/-- Nondegeneracy of the trace pairing on square matrices over `ℂ`:
if `trace (M * N) = 0` for all `N`, then `M = 0`. -/
theorem trace_mul_right_eq_zero_iff {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) :
    (∀ N : Matrix n n ℂ, Matrix.trace (M * N) = 0) ↔ M = 0 := by
  classical
  constructor
  · intro h; ext i j
    have hNM : Matrix.trace (Matrix.single j i (1 : ℂ) * M) = 0 :=
      (Matrix.trace_mul_comm M _).symm.trans (h _)
    simpa [Matrix.trace_single_mul (i := j) (j := i) (a := (1 : ℂ))] using hNM
  · intro h N; simp [h]

end Matrix
