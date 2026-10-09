/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.MPUCanonicalForm
import TNLean.MPS.MPU.PositiveCanonicalGauge

/-!
# Canonical form up to similarity

An MPU tensor in canonical form is similar, by one invertible bond matrix, to an MPU tensor in
canonical form II. The source passes to canonical form II "without loss of generality" by a gauge
transformation (arXiv:1703.09188, `Papers/1703.09188/paper_v2.tex`, lines 294 and 356); this file
states that gauge as a lemma (the chapter's Lemma "Canonical form up to similarity").

The normalized tensor `d^{-1/2} U` is normal (Proposition `prop:normal-tensor`). A positive
definite fixed point `σ` of the dual transfer map gives the left-canonical gauge
`σ^{1/2} A σ^{-1/2}`, and a unitary `V` diagonalizing the fixed point of the gauged transfer map
then gives canonical form II with one block filling the bond space. The similarity is
`X = V^† σ^{1/2}`.

## Main results

* `MPOTensor.IsMPU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm` — an MPU tensor in
  canonical form is `X⁻¹ U' X` for an invertible `X` and an MPU tensor `U'` in canonical
  form II.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace MPOTensor

variable {d D : ℕ}

/-- **Canonical form up to similarity.** An MPU tensor `U` in canonical form is similar to an MPU
tensor in canonical form II: there is an invertible bond matrix `X` such that `X U X⁻¹` is in
canonical form II. The similar tensor generates the same periodic operators as `U`.

Source: arXiv:1703.09188, `Papers/1703.09188/paper_v2.tex`, lines 294 and 356 (the gauge to
canonical form II taken without loss of generality); the chapter's Lemma "Canonical form up to
similarity". The proof follows the left-canonical gauge `σ^{1/2} A σ^{-1/2}` of the normal tensor
`A = d^{-1/2} U` by a unitary diagonalization of its fixed point. -/
theorem IsMPU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor) :
    ∃ X : GL (Fin D) ℂ, Nonempty (IsMPUCanonicalFormII (virtualSandwich
      (X : Matrix (Fin D) (Fin D) ℂ) U ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) := by
  have hNormal := hU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm hcf
  obtain ⟨σ, hσ, hσfix, -⟩ := hNormal.exists_tpGauge
  obtain ⟨V, hV, -⟩ := exists_canonicalFormII_positiveGauge U hU hNormal σ hσ hσfix
  let S : GL (Fin D) ℂ := Matrix.nonsingInvUnit (CFC.sqrt σ) hσ.isUnit_det_cfc_sqrt
  have hX : (((MPSTensor.unitaryGL V)⁻¹ * S : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * CFC.sqrt σ := rfl
  have hXinv : ((((MPSTensor.unitaryGL V)⁻¹ * S)⁻¹ : GL (Fin D) ℂ) :
      Matrix (Fin D) (Fin D) ℂ) = (CFC.sqrt σ)⁻¹ * (V : Matrix (Fin D) (Fin D) ℂ) := rfl
  refine ⟨(MPSTensor.unitaryGL V)⁻¹ * S, ?_⟩
  rw [hX, hXinv]
  convert hV using 3
  funext i j
  simp only [virtualSandwich_apply, Matrix.mul_assoc]

end MPOTensor
