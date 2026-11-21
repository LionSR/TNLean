/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.ZeroBoundary
import QICLean.Algebra.TraceReindex
import QICLean.Channel.MaximalOverlap

/-!
# Regional density matrices of pure vectors

Partial trace preserves positivity and the squared-norm trace of a pure-state
matrix. Consequently a unit vector gives trace-one regional density matrices,
nonnegative regional entropy, and zero entropy on the empty and full regions.
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
theorem trace_reducedState_eq_norm_sq (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    (ManyBody.regionState Ω A).trace = (‖Ω‖ : ℂ) ^ 2 := by
  rw [ManyBody.trace_regionState A Ω, Complex.ofReal_pow]

/-- Regional entropy of a unit vector is nonnegative.
Source: area-law `sec:prelim`, lines 10–25, entropy of normalized density operators. -/
theorem regionalEntropy_nonneg (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ)) :
    0 ≤ ManyBody.regionEntropy Ω A :=
  vonNeumannEntropy_nonneg_of_posSemidef_trace_one
    (ManyBody.regionState_posSemidef A Ω) (trace_reducedState Ω hΩ A)

/-- The empty region has zero entropy for a unit vector.
Source: area-law `sec:prelim`, lines 23–25, empty tensor products. -/
@[simp] theorem regionalEntropy_empty (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) :
    ManyBody.regionEntropy Ω ∅ = 0 := by
  exact ManyBody.regionEntropy_empty _ Ω hΩ

/-- The full region has zero entropy for a unit pure vector.
Source: area-law `sec:prelim`, lines 23–25, purity and empty complements. -/
@[simp] theorem regionalEntropy_univ (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) :
    ManyBody.regionEntropy Ω Finset.univ = 0 := by
  exact ManyBody.regionEntropy_univ _ Ω hΩ

end TNLean.PEPS.AreaLaw
