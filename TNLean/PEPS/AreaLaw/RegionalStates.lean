/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TheoremStatements
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

namespace TNLean.PEPS.AreaLaw

/-- Regional reductions of a pure vector are positive semidefinite.
Source: area-law `sec:prelim`, lines 10–25, normalized density operators
and partial trace; the positivity statement does not require normalization. -/
theorem reducedState_posSemidef (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    (reducedState Λ q Ω A).PosSemidef :=
  ((Matrix.posSemidef_vecMulVec_self_star (fun x ↦ Ω x)).submatrix
    (configurationSplit Λ q A).symm).partialTraceRight

/-- The trace of a reduced pure-state matrix is the squared norm of its vector.
Source: area-law `sec:prelim`, lines 10–25, normalization of density operators
and the one-dimensional empty tensor product. -/
theorem trace_reducedState (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (A : Finset (Site Λ)) :
    (reducedState Λ q Ω A).trace = (‖Ω‖ : ℂ) ^ 2 := by
  rw [reducedState, Matrix.trace_partialTraceRight]
  change (Matrix.reindex (configurationSplit Λ q A) (configurationSplit Λ q A)
    (Matrix.vecMulVec (fun x ↦ Ω x) (star (fun x ↦ Ω x)))).trace = _
  rw [Matrix.trace_reindex, Matrix.trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
  rfl

/-- A unit vector has trace-one regional density matrices.
Source: area-law `sec:prelim`, lines 10–25, normalized density operators. -/
theorem trace_reducedState_eq_one (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ)) :
    (reducedState Λ q Ω A).trace = 1 := by
  simpa [hΩ] using trace_reducedState Λ q Ω A

/-- Regional entropy of a unit vector is nonnegative.
Source: area-law `sec:prelim`, lines 10–25, entropy of normalized density operators. -/
theorem regionalEntropy_nonneg (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ)) :
    0 ≤ regionalEntropy Λ q Ω A :=
  vonNeumannEntropy_nonneg_of_posSemidef_trace_one
    (reducedState_posSemidef Λ q Ω A) (trace_reducedState_eq_one Λ q Ω hΩ A)

/-- The empty region has zero entropy for a unit vector.
Source: area-law `sec:prelim`, lines 23–25, empty tensor products. -/
@[simp] theorem regionalEntropy_empty (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) :
    regionalEntropy Λ q Ω ∅ = 0 := by
  apply vonNeumannEntropy_eq_zero_of_rank_le_one
    (reducedState_posSemidef Λ q Ω ∅) (trace_reducedState_eq_one Λ q Ω hΩ ∅)
  simpa using Matrix.rank_le_card_width (reducedState Λ q Ω ∅)

/-- The full region has zero entropy for a unit pure vector.
Source: area-law `sec:prelim`, lines 23–25, purity and empty complements. -/
@[simp] theorem regionalEntropy_univ (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) :
    regionalEntropy Λ q Ω Finset.univ = 0 := by
  apply vonNeumannEntropy_eq_zero_of_rank_le_one
    (reducedState_posSemidef Λ q Ω Finset.univ)
    (trace_reducedState_eq_one Λ q Ω hΩ Finset.univ)
  change (Matrix.partialTraceRight (Matrix.vecMulVec
    (fun x ↦ Ω ((configurationSplit Λ q Finset.univ).symm x))
    (star (fun x ↦ Ω ((configurationSplit Λ q Finset.univ).symm x))))).rank ≤ 1
  rw [Matrix.partialTraceRight_vecMulVec_eq]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width
      (Matrix.schmidtCoeffMatrix (fun x ↦ Ω ((configurationSplit Λ q Finset.univ).symm x))))

end TNLean.PEPS.AreaLaw
