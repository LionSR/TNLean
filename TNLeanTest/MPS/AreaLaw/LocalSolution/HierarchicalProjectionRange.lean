/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.HierarchicalProjection

/-! The second-level projection must exclude the kernel of the preceding projection,
even when the spectral window contains zero. The example uses the nonzero proper projection
`diag(1, 0)`, the zero operator, centre zero, and radius one. -/

open Matrix TNLean.MPS.AreaLaw.LocalSolution
open TNLean.MPS.AreaLaw.Hastings
open scoped Matrix.Norms.L2Operator

namespace TNLeanTest.HierarchicalProjectionRange

private def retained : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]

private theorem ambient_zero : windowProjection (0 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 1 := by
  simp [windowProjection, spectralCutoff]

-- The ambient window retains the second coordinate, which belongs to the kernel of Q.
example : windowProjection (retained * 0 * retained) 0 1 1 1 = 1 := by
  simp [ambient_zero]

private theorem compressed_zero : compressedWindowProjection retained 0 0 1 = retained := by
  simp [compressedWindowProjection, ambient_zero]

-- The restricted window retains the first coordinate and removes the second.
example : compressedWindowProjection retained 0 0 1 0 0 = 1 := by
  rw [compressed_zero]
  simp [retained]

example : compressedWindowProjection retained 0 0 1 1 1 = 0 := by
  rw [compressed_zero]
  simp [retained]

end TNLeanTest.HierarchicalProjectionRange
