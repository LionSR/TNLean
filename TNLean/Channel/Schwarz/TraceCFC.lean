/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Trace of the continuous functional calculus on a Hermitian matrix

Small helper lemma used in the `trace_rpow_*` convexity/concavity proofs: the
(real part of the) trace of `hA.cfc f` equals `∑ i, f (hA.eigenvalues i)`.

The proof combines the unitary-diagonal form of `Matrix.IsHermitian.cfc`
(see `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`) with
`Matrix.trace_mul_cycle` and `Matrix.trace_diagonal`, exactly the pattern used
by `Matrix.PosSemidef.trace_eq_zero_iff` in Mathlib.
-/

namespace Matrix
namespace IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the trace of `hA.cfc f` is the sum of `f` over the
eigenvalues of `A`.

This packages the standard calculation
`trace (U * diagonal (f ∘ λ) * U†) = ∑ i, f (λ i)` obtained from the spectral
theorem and `trace_mul_cycle`. -/
theorem trace_cfc_eq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (Matrix.trace (hA.cfc f)).re = ∑ i, f (hA.eigenvalues i) := by
  rw [IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rw [show (∑ i, (RCLike.ofReal ∘ f ∘ hA.eigenvalues) i : ℂ)
        = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) by
      push_cast [Function.comp_apply]; rfl]
  exact Complex.ofReal_re _

end IsHermitian
end Matrix
