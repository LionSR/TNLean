/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Basic Frobenius inner-product ingredients for square complex matrices

At present we only expose the positivity of the identity matrix, which is the
weight used to recover the standard Frobenius inner product on
`Matrix (Fin D) (Fin D) ℂ` via Mathlib's `Matrix.toMatrixInnerProductSpace`.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {D : ℕ}

/-- Positive-definiteness of the identity matrix, used to define the Frobenius inner product. -/
theorem frobenius_posDef_one :
    (1 : Matrix (Fin D) (Fin D) ℂ).PosDef := by
  classical
  simpa using (Matrix.PosDef.one (n := Fin D) (R := ℂ))

end Matrix
