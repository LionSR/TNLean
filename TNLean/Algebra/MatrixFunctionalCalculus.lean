import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.Matrix.Order

open scoped MatrixOrder

namespace TNLean

section

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Shared helper for the nonunital selfadjoint functional calculus on complex matrices. -/
noncomputable abbrev matrixNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint :=
  ContinuousFunctionalCalculus.toNonUnital

/-- Shared helper for the real nonnegative spectrum structure on complex matrices. -/
noncomputable abbrev matrixNonnegSpectrumClass :
    NonnegSpectrumClass ℝ (Matrix n n ℂ) :=
  Matrix.instNonnegSpectrumClass

end

end TNLean
