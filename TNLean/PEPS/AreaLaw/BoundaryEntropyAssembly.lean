/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.EntropyDimension

/-!
# The numerical entropy estimate for an ordered decomposition

The two-family entropy bound and the regional dimension bound imply an entropy
estimate linear in the number of cut edges whenever the residual site count and
the sum of the mutual-information errors have linear bounds. The constants in
the conclusion are computed from those two supplied estimates.

This proves only the final numerical implication. Construction of the ordered
decomposition and derivation of its residual and information estimates remain
necessary to establish the uniform ground-state area law.

## References

OpenAI, *A two-dimensional area law from a global spectral gap* (2026), proof of
Theorem 1.1, `10-geometry.tex`, lines 846–857, immutable source
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized; no OpenAI Lean proof text is reused.
-/

open scoped BigOperators

namespace TNLean.PEPS.AreaLaw

/-- The final numerical implication in the proof of the area law. Source:
proof of Theorem 1.1, `10-geometry.tex`, lines 846–857. The partition, its residual
site bound, and the total information-error bound are inputs; this theorem does
not assert their existence or prove the uniform ground-state area law. -/
theorem regionalEntropy_le_boundary_of_partition_estimates
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : StateSpace Λ q) (hΩ : ‖Ω‖ = 1) (A : Finset (Site Λ))
    (P : Geometry.OrderedTwoFamilyPartition A) (ε : Fin P.pieceCount → ℝ)
    (hε : ∀ i, FiniteProduct.mutualInformation (fun _ : Site Λ ↦ Fin q) Ω (P.piece i)
      (Aᶜ ∪ P.earlierSameFamily i) ≤ ε i)
    (cD cE : ℝ)
    (hD : (P.residual.card : ℝ) ≤ cD * (edgeBoundary Λ A).card)
    (hE : (∑ i, ε i) ≤ cE * (edgeBoundary Λ A).card) :
    regionalEntropy Λ q Ω A ≤
      (cD * Real.log q + cE / 2) * (edgeBoundary Λ A).card := by
  have h := regionalEntropy_le_residual_add_half_sum Λ q Ω hΩ A P ε hε
  have hdim := regionalEntropy_le_card_mul_log Λ q Ω hΩ P.residual
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hD' := mul_le_mul_of_nonneg_right hD hlog
  have hE' := mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith only [h, hdim, hD', hE']

end TNLean.PEPS.AreaLaw
