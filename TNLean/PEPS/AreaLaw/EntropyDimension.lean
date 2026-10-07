/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.TwoFamilies

/-!
# Entropy bounded by the number of sites

For a unit vector with local dimension \(q\), the entropy of a region is at most
its number of sites times \(\log q\). The regional density matrix has trace one;
its rank is at most the dimension \(q^{|A|}\) of the regional Hilbert space.

## References

OpenAI, *A two-dimensional area law from a global spectral gap* (2026),
proof of Theorem 1.1, `10-geometry.tex`, lines 846–851, immutable source
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently proved from the mathematical argument; no OpenAI Lean proof text
is reused. This result does not require a Hamiltonian or spectral gap.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/10-geometry.tex
Labels: thm:area, sec:geometry.
Provenance-ID: 8759-tn-entropy-dimension-01
Downstream declaration:
TNLean.PEPS.AreaLaw.regionalEntropy_le_card_mul_log
-/

namespace TNLean.PEPS.AreaLaw

/-- A normalized regional state's entropy is at most its site count times the
logarithm of the local dimension. Source: area-law proof of Theorem 1.1,
`10-geometry.tex`, lines 846–851. The estimate includes empty regions and `q = 1`. -/
theorem regionalEntropy_le_card_mul_log
    (Λ : Finset (ℤ × ℤ)) (q : ℕ)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ)) :
    regionalEntropy Λ q Ω A ≤ (A.card : ℝ) * Real.log q := by
  rw [regionalEntropy_eq_finiteProduct]
  have hρ := FiniteProduct.reducedPure_posSemidef (fun _ : Site Λ ↦ Fin q) Ω A
  have htr := FiniteProduct.trace_reducedPure (fun _ : Site Λ ↦ Fin q) Ω hΩ A
  refine (vonNeumannEntropy_le_log_rank hρ htr).trans ?_
  have h := Real.log_le_log (Nat.cast_pos.mpr (hρ.rank_pos_of_trace_one htr))
    (Nat.cast_le.mpr (Matrix.rank_le_card_width
      (FiniteProduct.reducedPure (fun _ : Site Λ ↦ Fin q) Ω A)))
  simpa [Nat.cast_pow, Real.log_pow] using h

end TNLean.PEPS.AreaLaw
