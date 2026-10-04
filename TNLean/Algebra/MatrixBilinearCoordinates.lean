/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Bilinear maps with paired matrix columns

A matrix whose columns are indexed by pairs determines a vector-valued bilinear
map. Evaluation of this map is multiplication by the vector of pairwise products.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open scoped Matrix

namespace Matrix

/-- Evaluation of a vector-valued bilinear map represented by paired columns. -/
theorem toLinearMap₂'_apply_mulVec_prod
    {R n m k : Type*} [CommSemiring R] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (M : Matrix k (n × m) R) (x : n → R) (y : m → R) :
    Matrix.toLinearMap₂' R (Matrix.of fun a b => fun i => M i (a, b)) x y =
      M *ᵥ (fun ab => x ab.1 * y ab.2) := by
  rw [Matrix.toLinearMap₂'_apply (R := R)]
  ext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.of_apply, mul_assoc, mul_comm]

end Matrix
