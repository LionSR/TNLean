/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CornerCompression
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

* `TNLean.sandwichedRenyiTwoTrace_partialTraces_kronecker_le_operatorSchmidtRank`
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
theorem sandwichedRenyiTwoTrace_partialTraces_kronecker_le_operatorSchmidtRank
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ : ρ.PosSemidef) :
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) ≤
      Matrix.operatorSchmidtRank ρ := by
  let hA : (partialTraceRight ρ).PosSemidef := hρ.partialTraceRight
  let hB : (partialTraceLeft ρ).PosSemidef := hρ.partialTraceLeft
  let PA : Matrix (Fin dA) (Fin dA) ℂ :=
    (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj
  let PB : Matrix (Fin dB) (Fin dB) ℂ :=
    (Matrix.PosSemidef.partialTraceLeft hρ).isHermitian.supportProj
  have hPA : IsOrthogonalProjection PA := by
    exact ⟨(Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj_isHermitian,
      (Matrix.PosSemidef.partialTraceRight hρ).isHermitian.supportProj_idem⟩
  have hPB : IsOrthogonalProjection PB := by
    exact ⟨(Matrix.PosSemidef.partialTraceLeft hρ).isHermitian.supportProj_isHermitian,
      (Matrix.PosSemidef.partialTraceLeft hρ).isHermitian.supportProj_idem⟩
  have hPAA : PA = hA.supportProj := by
    dsimp only [PA]
    exact (Matrix.PosSemidef.partialTraceRight hρ).supportProj_congr hA rfl
  have hPBB : PB = hB.supportProj := by
    dsimp only [PB]
    exact (Matrix.PosSemidef.partialTraceLeft hρ).supportProj_congr hB rfl
  let SA := ProjectionSpectralSplit.ofOrthogonalProjection PA hPA
  let SB := ProjectionSpectralSplit.ofOrthogonalProjection PB hPB
  letI : Fintype SA.S := SA.instFintypeS
  letI : Fintype SA.T := SA.instFintypeT
  letI : DecidableEq SA.S := SA.instDecidableEqS
  letI : DecidableEq SA.T := SA.instDecidableEqT
  letI : Fintype SB.S := SB.instFintypeS
  letI : Fintype SB.T := SB.instFintypeT
  letI : DecidableEq SB.S := SB.instDecidableEqS
  letI : DecidableEq SB.T := SB.instDecidableEqT
  let VA : Matrix (Fin dA) (Fin SA.n) ℂ :=
    cornerCompressionIsometry SA.Umat SA.eST SA.eS
  let VB : Matrix (Fin dB) (Fin SB.n) ℂ :=
    cornerCompressionIsometry SB.Umat SB.eST SB.eS
  have hVA : VAᴴ * VA = 1 :=
    cornerCompressionIsometry_conjTranspose_mul SA.Umat SA.eST SA.eS SA.hU'U
  have hVB : VBᴴ * VB = 1 :=
    cornerCompressionIsometry_conjTranspose_mul SB.Umat SB.eST SB.eS SB.hU'U
  have hRangeA : VA * VAᴴ = PA := by
    calc
      VA * VAᴴ = VA * 1 * VAᴴ := by rw [Matrix.mul_one]
      _ = cornerCompressionExpand SA.Umat SA.eST SA.eS 1 :=
        (cornerCompressionExpand_eq_isometry SA.Umat SA.eST SA.eS 1).symm
      _ = PA := cornerCompressionExpand_one PA (SA.Umatᴴ * PA * SA.Umat)
        SA.Umat SA.eST SA.eS
        (Matrix.fromBlocks (1 : Matrix SA.S SA.S ℂ) 0 0 (0 : Matrix SA.T SA.T ℂ))
        rfl SA.hP_decomp SA.hPdiag_back
  have hRangeB : VB * VBᴴ = PB := by
    calc
      VB * VBᴴ = VB * 1 * VBᴴ := by rw [Matrix.mul_one]
      _ = cornerCompressionExpand SB.Umat SB.eST SB.eS 1 :=
        (cornerCompressionExpand_eq_isometry SB.Umat SB.eST SB.eS 1).symm
      _ = PB := cornerCompressionExpand_one PB (SB.Umatᴴ * PB * SB.Umat)
        SB.Umat SB.eST SB.eS
        (Matrix.fromBlocks (1 : Matrix SB.S SB.S ℂ) 0 0 (0 : Matrix SB.T SB.T ℂ))
        rfl SB.hP_decomp SB.hPdiag_back
  let V : Matrix (Fin dA × Fin dB) (Fin SA.n × Fin SB.n) ℂ := VA ⊗ₖ VB
  let ρc : Matrix (Fin SA.n × Fin SB.n) (Fin SA.n × Fin SB.n) ℂ :=
    Vᴴ * ρ * V
  have hV : Vᴴ * V = 1 := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hVA, hVB, Matrix.one_kronecker_one]
  have hRange : V * Vᴴ =
      (hA.kronecker hB).supportProj := by
    dsimp only [V]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hRangeA, hRangeB, hPAA, hPBB, hA.supportProj_kronecker hB]
  have hρc : ρc.PosSemidef := by
    exact hρ.conjTranspose_mul_mul_same V
  have hMarginals :
      (partialTraceRight ρc).PosDef ∧ (partialTraceLeft ρc).PosDef := by
    exact hρ.marginalSupport_compression_marginals_posDef
      VA VB hVA hVB (by simpa only [PA] using hRangeA) (by simpa only [PB] using hRangeB)
  have hMargA : partialTraceRight ρc = VAᴴ * partialTraceRight ρ * VA := by
    exact hρ.partialTraceRight_marginalSupport_compression
      VA VB hVA hVB (by simpa only [PA] using hRangeA) (by simpa only [PB] using hRangeB)
  have hMargB : partialTraceLeft ρc = VBᴴ * partialTraceLeft ρ * VB := by
    exact hρ.partialTraceLeft_marginalSupport_compression
      VA VB hVA hVB (by simpa only [PA] using hRangeA) (by simpa only [PB] using hRangeB)
  let ω := partialTraceRight ρ ⊗ₖ partialTraceLeft ρ
  have hω : ω.PosSemidef := hA.kronecker hB
  have hρPA : ρ * (PA ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) = ρ := by
    simpa only [PA, Matrix.leftKroneckerEmbed_apply] using
      hρ.mul_leftKroneckerEmbed_supportProj_self
  have hρPB : ρ * ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ PB) = ρ := by
    simpa only [PB, Matrix.rightKroneckerEmbed_apply] using
      hρ.mul_rightKroneckerEmbed_supportProj_self
  have hρP : ρ * (PA ⊗ₖ PB) = ρ := by
    rw [show PA ⊗ₖ PB = ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ PB) *
        (PA ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) by
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]]
    rw [← Matrix.mul_assoc, hρPB, hρPA]
  have hker : ∀ v : Fin dA × Fin dB → ℂ, ω *ᵥ v = 0 → ρ *ᵥ v = 0 := by
    intro v hv
    have hPv := hω.supportProj_mulVec_eq_zero_of_mulVec_eq_zero v hv
    have hsupport : hω.supportProj = PA ⊗ₖ PB := by
      calc
        hω.supportProj = (hA.kronecker hB).supportProj :=
          hω.supportProj_congr (hA.kronecker hB) rfl
        _ = hA.supportProj ⊗ₖ hB.supportProj := hA.supportProj_kronecker hB
        _ = PA ⊗ₖ PB := by rw [hPAA, hPBB]
    rw [hsupport] at hPv
    rw [← hρP, ← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_zero]
  have hωc : Vᴴ * ω * V = partialTraceRight ρc ⊗ₖ partialTraceLeft ρc := by
    dsimp only [V, ω]
    rw [Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← hMargA, ← hMargB]
  have hQ2 := sandwichedRenyiTwoTrace_support_compression
    hρ hω hker V hV hRange
  have hOSR := hρ.operatorSchmidtRank_marginalSupport_compression
    VA VB hVA hVB (by simpa only [PA] using hRangeA) (by simpa only [PB] using hRangeB)
  calc
    sandwichedRenyiTwoTrace ρ
        (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) =
      sandwichedRenyiTwoTrace ρc
        (partialTraceRight ρc ⊗ₖ partialTraceLeft ρc) := by
          rw [show partialTraceRight ρ ⊗ₖ partialTraceLeft ρ = ω from rfl,
            hQ2, hωc]
    _ ≤ Matrix.operatorSchmidtRank ρc :=
      sandwichedRenyiTwoTrace_partialTraces_kronecker_le_operatorSchmidtRank_of_posDef
        ρc hρc hMarginals.1 hMarginals.2
    _ = Matrix.operatorSchmidtRank ρ := by
      exact_mod_cast hOSR

end TNLean
