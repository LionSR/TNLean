/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.MarginalSupportWhitenedChoi
import TNLean.Channel.Schwarz.SSAEqualityDPI
import TNLean.Channel.Schwarz.SSAEqualityPetzRecovery

/-!
# Mutual information from operator-Schmidt rank

This file bounds the mutual information of a finite-dimensional bipartite
density operator by the logarithm of its ordinary operator-Schmidt rank.

## Main results

* `TNLean.quantumRelativeEntropy_product_marginals_eq_mutualInformation`
  identifies mutual information with relative entropy from the product of the
  marginals.
* `TNLean.Entropy.mutualInformation_le_log_operatorSchmidtRank` proves the
  operator-Schmidt-rank bound.

## References

* Hayden, Jozsa, Petz, and Winter, arXiv:quant-ph/0304007v2, p. 3,
  equation (4).
* Müller-Lennert, Dupuis, Szehr, Fehr, and Tomamichel,
  arXiv:1306.3142v4, Definition 5 and Lemma 19.
* Beigi, arXiv:1306.5920, Theorem 6, equation (18).
-/

open scoped Kronecker MatrixOrder
open Matrix

noncomputable section

namespace TNLean

variable {dA dB : ℕ}

/-- Mutual information is relative entropy from the product of the two
marginals.

Source: Hayden--Jozsa--Petz--Winter, arXiv:quant-ph/0304007v2, p. 3,
equation (4). -/
theorem quantumRelativeEntropy_product_marginals_eq_mutualInformation
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (hρ : ρ.PosSemidef) :
    quantumRelativeEntropy ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) =
      Entropy.mutualInformation ρ hρ.isHermitian := by
  simpa only [Entropy.mutualInformation, Matrix.traceRight, Matrix.traceLeft]
    using quantumRelativeEntropy_product_marginals hρ

/-- The mutual information of a finite-dimensional bipartite density operator
is at most the logarithm of its ordinary operator-Schmidt rank.

This is a finite-dimensional consequence of the order-two sandwiched
relative-entropy comparison of Müller-Lennert et al., arXiv:1306.3142v4,
Definition 5 and Lemma 19, together with Beigi, arXiv:1306.5920, Theorem 6,
equation (18). -/
theorem Entropy.mutualInformation_le_log_operatorSchmidtRank
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) :
    Entropy.mutualInformation ρ hρ.isHermitian ≤
      Real.log (Matrix.operatorSchmidtRank ρ) := by
  let ω := partialTraceRight ρ ⊗ₖ partialTraceLeft ρ
  have hA : (partialTraceRight ρ).PosSemidef := hρ.partialTraceRight
  have hB : (partialTraceLeft ρ).PosSemidef := hρ.partialTraceLeft
  have hω : ω.PosSemidef := hA.kronecker hB
  have hωtr : ω.trace = 1 := by
    dsimp only [ω]
    rw [Matrix.trace_kronecker, Matrix.trace_partialTraceRight,
      Matrix.trace_partialTraceLeft, hρtr, one_mul]
  have hρ_ne : ρ ≠ 0 := by
    intro hρzero
    rw [hρzero, Matrix.trace_zero] at hρtr
    exact zero_ne_one hρtr
  have hRankPos : 0 < Matrix.operatorSchmidtRank ρ :=
    (Matrix.operatorSchmidtRank_pos_iff ρ).2 hρ_ne
  have hRankOne : (1 : ℝ) ≤ Matrix.operatorSchmidtRank ρ := by
    exact_mod_cast hRankPos
  have hQ2nonneg :
      0 ≤ sandwichedRenyiTwoTrace ρ ω :=
    sandwichedRenyiTwoTrace_nonneg hρ hω
  have hQ2le :
      sandwichedRenyiTwoTrace ρ ω ≤ Matrix.operatorSchmidtRank ρ :=
    sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank ρ hρ
  rw [← quantumRelativeEntropy_product_marginals_eq_mutualInformation hρ]
  calc
    quantumRelativeEntropy ρ ω ≤
        Real.log (sandwichedRenyiTwoTrace ρ ω) :=
      quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace
        hρ hω hρtr hωtr (Matrix.product_marginal_support hρ)
    _ ≤ Real.log (Matrix.operatorSchmidtRank ρ) := by
      by_cases hQ2zero : sandwichedRenyiTwoTrace ρ ω = 0
      · rw [hQ2zero, Real.log_zero]
        exact Real.log_nonneg hRankOne
      · exact Real.log_le_log (lt_of_le_of_ne hQ2nonneg (Ne.symm hQ2zero)) hQ2le

end TNLean
