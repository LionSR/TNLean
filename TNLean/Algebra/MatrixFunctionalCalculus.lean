import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order

/-!
# Matrix Functional Calculus Scopes

This helper module centralizes the real matrix functional-calculus instances
used throughout the Lean 4.29 upgrade work, so downstream files can opt into
them via `open scoped TNMatrixCFC`.
-/

open scoped MatrixOrder

namespace TNLean
end TNLean

namespace TNMatrixCFC

scoped instance (n : Type*) [Fintype n] [DecidableEq n] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital

/-- Scoped real nonnegative-spectrum instance for complex matrices. -/
scoped instance (n : Type*) [Fintype n] [DecidableEq n] :
    NonnegSpectrumClass ℝ (Matrix n n ℂ) :=
  Matrix.instNonnegSpectrumClass

end TNMatrixCFC
