/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Tactic.Attr.Register

/-!
# Simp attributes for tensor-network proofs

This file registers simp sets independently of their rewriting lemmas.
-/

/-- Move scalars out of matrix products and cancel nested reciprocal scalar actions.

With `hβ : β ≠ 0`, `simp (disch := exact hβ) only [matrix_reciprocal_smul]` replaces the repeated
rewrites by `Matrix.smul_mul`, `Matrix.mul_smul`, `inv_smul_smul₀`, and
`smul_inv_smul₀`. The normal form removes reciprocal scalar pairs without combining
arbitrary nested actions via `smul_smul`.
-/
register_simp_attr matrix_reciprocal_smul
