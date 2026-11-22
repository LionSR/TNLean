/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Regions.ZeroBoundary
import QICLean.Algebra.Matrix.MatrixReindex
import QICLean.Channel.Schmidt.MaximalOverlap

/-!
# Regional density matrices of pure vectors

Partial trace preserves positivity and the squared-norm trace of a pure-state
matrix. Consequently a unit vector gives trace-one regional density matrices and
nonnegative regional entropy; the zero entropy of the empty and full regions is
QICLean's `ManyBody.regionEntropy_empty` and `ManyBody.regionEntropy_univ`.
The configuration splitting includes the one-dimensional empty tensor product.
No gap or locality assumption is needed for these finite-dimensional identities.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 2 (`sec:prelim`), lines 10–25.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped ComplexOrder
open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw

/-- The trace of a reduced pure-state matrix is the squared norm of its vector.
Source: area-law `sec:prelim`, lines 10–25, normalization of density operators
and the one-dimensional empty tensor product. -/
theorem trace_regionState_eq_norm_sq (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    (ManyBody.regionState Ω A).trace = (‖Ω‖ : ℂ) ^ 2 := by
  rw [ManyBody.trace_regionState A Ω, Complex.ofReal_pow]

/-- Regional entropy of a unit vector is nonnegative.
Source: area-law `sec:prelim`, lines 10–25, entropy of normalized density operators. -/
theorem regionEntropy_nonneg (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ)) :
    0 ≤ ManyBody.regionEntropy Ω A :=
  vonNeumannEntropy_nonneg_of_posSemidef_trace_one
    (ManyBody.regionState_posSemidef A Ω) (ManyBody.trace_regionState_eq_one hΩ (D := A))

end TNLean.PEPS.AreaLaw
