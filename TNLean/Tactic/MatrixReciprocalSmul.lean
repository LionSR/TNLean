/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Data.Matrix.Mul
import TNLean.Tactic.Attr

/-!
# Reciprocal scalar cancellation in matrix products

The `matrix_reciprocal_smul` simp set moves scalars out of matrix products and
cancels nested actions by a nonzero scalar and its inverse, in either order.
Use `simp (disch := exact hβ) only [matrix_reciprocal_smul]` with `hβ : β ≠ 0`.

The set deliberately excludes `smul_smul`: combining nested actions would hide the
reciprocal pairs from the cancellation lemmas.
-/

attribute [matrix_reciprocal_smul] Matrix.smul_mul Matrix.mul_smul
  inv_smul_smul₀ smul_inv_smul₀
