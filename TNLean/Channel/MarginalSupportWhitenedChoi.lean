/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.SupportCompressedEntropy
import TNLean.Channel.FaithfulMarginalWhitenedChoi
import TNLean.Channel.MarginalSupportAbsorption

/-!
# Marginal-support whitening

A positive-semidefinite bipartite operator is compressed simultaneously to the
supports of its two marginals.  The compressed marginals are faithful, while
the order-two sandwiched trace and ordinary operator-Schmidt rank are unchanged.
The support coordinate spaces may both be zero-dimensional.

## Main declaration

* `TNLean.sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank`
  is the arbitrary-support whitened Choi estimate.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

noncomputable section

namespace TNLean

variable {dA dB : ℕ}

/-- For every positive-semidefinite bipartite operator, the order-two
sandwiched trace against the product of its marginals is at most its ordinary
operator-Schmidt rank.

No normalization or positive-dimension assumption is needed.  Simultaneous
compression to the two marginal supports includes the cases where either
support coordinate space is `Fin 0`. -/
theorem sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.PosSemidef) :
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) ≤
      Matrix.operatorSchmidtRank ρ := by
  let hA : (partialTraceRight ρ).PosSemidef := hρ.partialTraceRight
  let hB : (partialTraceLeft ρ).PosSemidef := hρ.partialTraceLeft
  obtain ⟨kA, VA, hVA, hRangeA⟩ :=
    hA.isOrthogonalProjection_supportProj.exists_range_isometry
  obtain ⟨kB, VB, hVB, hRangeB⟩ :=
    hB.isOrthogonalProjection_supportProj.exists_range_isometry
  let V : Matrix (Fin dA × Fin dB) (Fin kA × Fin kB) ℂ := VA ⊗ₖ VB
  let ρc : Matrix (Fin kA × Fin kB) (Fin kA × Fin kB) ℂ := Vᴴ * ρ * V
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hVA, hVB, Matrix.one_kronecker_one]
  have hRange : V * Vᴴ = (hA.kronecker hB).supportProj := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hRangeA, hRangeB, hA.supportProj_kronecker hB]
  have hρc : ρc.PosSemidef := hρ.conjTranspose_mul_mul_same V
  have hMarginals :
      (partialTraceRight ρc).PosDef ∧ (partialTraceLeft ρc).PosDef :=
    hρ.marginalSupport_compression_marginals_posDef
      VA VB hVA hVB hRangeA hRangeB
  have hMargA : partialTraceRight ρc = VAᴴ * partialTraceRight ρ * VA :=
    hρ.partialTraceRight_marginalSupport_compression
      VA VB hVA hVB hRangeA hRangeB
  have hMargB : partialTraceLeft ρc = VBᴴ * partialTraceLeft ρ * VB :=
    hρ.partialTraceLeft_marginalSupport_compression
      VA VB hVA hVB hRangeA hRangeB
  let ω := partialTraceRight ρ ⊗ₖ partialTraceLeft ρ
  have hω : ω.PosSemidef := hA.kronecker hB
  have hker : ∀ v : Fin dA × Fin dB → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0 := by
    simpa only [ω] using hρ.productMarginals_kernel_le
  have hωc : Vᴴ * ω * V = partialTraceRight ρc ⊗ₖ partialTraceLeft ρc := by
    dsimp only [V, ω]
    rw [Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← hMargA, ← hMargB]
  have hQ2 := sandwichedRenyiTwoTrace_support_compression
    hρ hω hker V hV hRange
  have hOSR := hρ.operatorSchmidtRank_marginalSupport_compression
    VA VB hVA hVB hRangeA hRangeB
  calc
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) =
      sandwichedRenyiTwoTrace ρc
        (partialTraceRight ρc ⊗ₖ partialTraceLeft ρc) := by
          rw [show partialTraceRight ρ ⊗ₖ partialTraceLeft ρ = ω from rfl,
            hQ2, hωc]
    _ ≤ Matrix.operatorSchmidtRank ρc :=
      sandwichedRenyiTwoTrace_product_marginals_le_operatorSchmidtRank_of_marginals_posDef
        ρc hρc hMarginals.1 hMarginals.2
    _ = Matrix.operatorSchmidtRank ρ := by exact_mod_cast hOSR

end TNLean
