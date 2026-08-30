/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import QICLean.Channel.MaximallyEntangled

/-!
# Unitarity of the tensor-factor swap matrix

This file packages the self-adjoint involution property of QICLean's tensor-factor
swap matrix as unitarity between its product-coordinate spaces.

## Main result

* `Matrix.swapMatrix_isUnitaryBetween`: the tensor-factor swap matrix is unitary between
  its source and target product-coordinate orders.
-/

namespace Matrix

/-- The tensor-factor swap matrix is unitary between its product-coordinate spaces.

With columns as source coordinates and rows as target coordinates, `swapMatrix d` sends the
source coordinate `(i, j)` to the target coordinate `(j, i)`. This is the exchange matrix
used in the shift-MPU source factors of arXiv:1703.09188, equations `eq:SF_u1_u3`,
`eq:uv2_U2`, and `eq:uv2_U3` (lines 2009--2034), and as the endpoint of the
unitary interpolation at lines 2148--2150. -/
theorem swapMatrix_isUnitaryBetween (d : ℕ) :
    (swapMatrix d).IsUnitaryBetween := by
  rw [IsUnitaryBetween, IsIsometry, IsCoisometry, swapMatrix_conjTranspose]
  exact ⟨swapMatrix_mul_self, swapMatrix_mul_self⟩

end Matrix
