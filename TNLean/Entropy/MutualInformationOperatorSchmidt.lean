/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.EntropyReindex
import TNLean.Channel.MarginalSupportWhitenedChoi
import TNLean.Entropy.MutualInformationBasic
import TNLean.Entropy.ProductMarginals

/-!
# Mutual information and operator-Schmidt rank

This file bounds the mutual information of a bipartite density matrix by the
natural logarithm of its ordinary operator-Schmidt rank. The proof identifies
mutual information with relative entropy against the product of the marginals,
compares relative entropy with the order-two sandwiched trace functional, and
uses the whitened Choi estimate for that functional.

## Main declaration

* `Entropy.mutualInformation_le_log_operatorSchmidtRank`: for every bipartite
  density matrix $\rho$, one has $I(A:B)_\rho\leq\log\operatorname{OSR}(\rho)$.
-/

open scoped Matrix ComplexOrder Kronecker
open Matrix

noncomputable section

namespace Entropy

variable {dA dB : ℕ}

/-- The mutual information of a bipartite density matrix is at most the natural
logarithm of its ordinary operator-Schmidt rank:
\[
  I(A:B)_\rho\leq\log\operatorname{OSR}(\rho).
\]

No positive-dimension or faithful-marginal assumption is needed. In particular,
the statement remains valid for all empty-index cases allowed by its hypotheses. -/
theorem mutualInformation_le_log_operatorSchmidtRank
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.PosSemidef ∧ ρ.trace = 1) :
    Entropy.mutualInformation ρ hρ.1.isHermitian ≤
      Real.log (Matrix.operatorSchmidtRank ρ) := by
  let ω := Matrix.partialTraceRight ρ ⊗ₖ Matrix.partialTraceLeft ρ
  have hω : ω.PosSemidef := hρ.1.partialTraceRight.kronecker hρ.1.partialTraceLeft
  have hωtr : ω.trace = 1 := by
    dsimp only [ω]
    rw [Matrix.trace_kronecker, Matrix.trace_partialTraceRight,
      Matrix.trace_partialTraceLeft, hρ.2, one_mul]
  have hker : ∀ v : Fin dA × Fin dB → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0 := by
    simpa only [ω] using hρ.1.productMarginals_kernel_le
  let e : (Fin dA × Fin dB) ≃ Fin (dA * dB) := finProdFinEquiv
  let ρ' := ρ.submatrix e.symm e.symm
  let ω' := ω.submatrix e.symm e.symm
  have hρ' : ρ'.PosSemidef := hρ.1.submatrix e.symm
  have hω' : ω'.PosSemidef := hω.submatrix e.symm
  have hρtr' : ρ'.trace = 1 := by
    dsimp only [ρ']
    rw [Matrix.trace_submatrix_equiv, hρ.2]
  have hωtr' : ω'.trace = 1 := by
    dsimp only [ω']
    rw [Matrix.trace_submatrix_equiv, hωtr]
  have hker' : ∀ v : Fin (dA * dB) → ℂ, ω' *ᵥ v = 0 → ρ' *ᵥ v = 0 := by
    simpa only [ρ', ω'] using Matrix.mulVec_submatrix_support e hker
  have hrelative' :
      quantumRelativeEntropy ρ' ω' ≤ Real.log (TNLean.sandwichedRenyiTwoTrace ρ' ω') :=
    TNLean.quantumRelativeEntropy_le_log_sandwichedRenyiTwoTrace
      hρ' hω' hρtr' hωtr' hker'
  have hrelative :
      quantumRelativeEntropy ρ ω ≤ Real.log (TNLean.sandwichedRenyiTwoTrace ρ ω) := by
    calc
      quantumRelativeEntropy ρ ω = quantumRelativeEntropy ρ' ω' :=
        (Matrix.quantumRelativeEntropy_submatrix_equiv
          hρ.1.isHermitian hω.isHermitian e).symm
      _ ≤ Real.log (TNLean.sandwichedRenyiTwoTrace ρ' ω') := hrelative'
      _ = Real.log (TNLean.sandwichedRenyiTwoTrace ρ ω) := congrArg Real.log
        (TNLean.sandwichedRenyiTwoTrace_submatrix_equiv hω e)
  have hMI :
      Entropy.mutualInformation ρ hρ.1.isHermitian = quantumRelativeEntropy ρ ω := by
    dsimp only [ω]
    symm
    exact quantumRelativeEntropy_product_marginals hρ.1
  rw [hMI]
  let q := TNLean.sandwichedRenyiTwoTrace ρ ω
  have hqnonneg : 0 ≤ q := by
    change 0 ≤ TNLean.sandwichedRenyiTwoTrace ρ ω
    rw [← TNLean.sandwichedRenyiTwoTrace_submatrix_equiv hω e]
    exact TNLean.sandwichedRenyiTwoTrace_nonneg hρ' hω'
  have hqle : q ≤ Matrix.operatorSchmidtRank ρ := by
    simpa only [q, ω] using
      TNLean.sandwichedRenyiTwoTrace_partialTraces_kronecker_le_operatorSchmidtRank
        ρ hρ.1
  have hρne : ρ ≠ 0 := by
    intro hzero
    have : (0 : ℂ) = 1 := by simpa only [hzero, Matrix.trace_zero] using hρ.2
    exact zero_ne_one this
  have hrankpos : 0 < Matrix.operatorSchmidtRank ρ :=
    Matrix.operatorSchmidtRank_pos_of_ne_zero ρ hρne
  by_cases hqzero : q = 0
  · have hrelative_zero : quantumRelativeEntropy ρ ω ≤ 0 := by
      simpa only [q, hqzero, Real.log_zero] using hrelative
    exact hrelative_zero.trans (Real.log_nonneg (by exact_mod_cast hrankpos))
  · exact hrelative.trans (Real.log_le_log (lt_of_le_of_ne hqnonneg (Ne.symm hqzero)) hqle)

end Entropy
