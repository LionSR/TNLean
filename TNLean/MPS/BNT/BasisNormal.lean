import TNLean.MPS.Core.MultiBlock

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Vandermonde separation for canonical-form weights

This file contains the purely algebraic Vandermonde separation lemma for distinct
canonical-form weights. The main BNT comparison route uses eventual linear independence from
overlap orthogonality; this file only records the scalar finite-dimensional separation step used
elsewhere in the block-permutation discussion.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- The Vandermonde separation lemma: if the scaling factors `μ k` are distinct,
then any linear relation `∑ k, c k * (μ k) ^ N = 0` holding for `N = 0, …, r-1`
forces all coefficients `c k` to vanish. -/
lemma vandermonde_separation (C : CanonicalForm d)
    (hμ : Function.Injective C.μ)
    (c : Fin C.numBlocks → ℂ)
    (hc : ∀ N : Fin C.numBlocks,
      (∑ k : Fin C.numBlocks, c k * (C.μ k) ^ (N : ℕ)) = 0) :
    c = 0 := by
  simpa using Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hμ hc

end MPSTensor
