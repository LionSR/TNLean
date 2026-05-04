import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order

/-!
# Matrix Functional Calculus Scopes

This module provides the real matrix functional-calculus instances
used throughout the Lean 4.29 upgrade, so downstream files can opt into
them via `open scoped TNMatrixCFC`.
-/

open scoped MatrixOrder

namespace TNLean
end TNLean

namespace TNMatrixCFC

scoped instance (n : Type*) [Fintype n] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint := by
  classical
  exact ContinuousFunctionalCalculus.toNonUnital

/-- Scoped real nonnegative-spectrum instance for complex matrices. -/
scoped instance (n : Type*) [Fintype n] :
    NonnegSpectrumClass ℝ (Matrix n n ℂ) := by
  classical
  exact Matrix.instNonnegSpectrumClass

end TNMatrixCFC
