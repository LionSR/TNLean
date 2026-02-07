import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped Matrix BigOperators

namespace Matrix

/-- Nondegeneracy of the trace pairing on square matrices over `ℂ`:
if `trace (M * N) = 0` for all `N`, then `M = 0`. -/
theorem trace_mul_right_eq_zero_iff {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) :
    (∀ N : Matrix n n ℂ, Matrix.trace (M * N) = 0) ↔ M = 0 := by
  classical
  constructor
  · intro h
    ext i j
    have hMN : Matrix.trace (M * Matrix.single j i (1 : ℂ)) = 0 :=
      h (Matrix.single j i (1 : ℂ))
    have hNM : Matrix.trace (Matrix.single j i (1 : ℂ) * M) = 0 := by
      -- Swap the factors using cyclicity of trace.
      exact (Matrix.trace_mul_comm M (Matrix.single j i (1 : ℂ))).symm.trans hMN
    -- Evaluate the trace of `single * M`.
    have hentry : (1 : ℂ) • M i j = 0 := by
      -- `trace (single j i 1 * M) = 1 • M i j`.
      simpa [Matrix.trace_single_mul (i := j) (j := i) (a := (1 : ℂ)) (x := M)] using hNM
    simpa using hentry
  · intro h N
    simp [h]

end Matrix
