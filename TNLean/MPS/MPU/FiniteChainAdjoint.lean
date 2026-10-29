/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.FiniteChainConjugation
import TNLean.MPS.MPU.SourceFactorContraction

/-!
# Actual finite-chain conjugation for the physical adjoint

The physical adjoint tensor produces the adjoint of the actual periodic
matrix without reflecting the physical chain. Consequently its finite
conjugation is the inverse finite conjugation of the original MPU.

Source: arXiv:1703.09188, finite unitary conjugation in eq:appendix-1,
lines 2300--2306; physical adjoint in arXiv:1606.00608, Appendix C.2.
-/

namespace SpinChain

/-- The actual finite matrix of the physical adjoint tensor is the
adjoint finite matrix, in the same integer interval coordinates.
Source: arXiv:1606.00608, Appendix C.2, lines 1634--1689. -/
theorem finiteChainMPOMatrix_physicalAdjointTensor {d D : ℕ}
    (U : MPOTensor d D) (N : ℕ) (b : ℤ) :
    finiteChainMPOMatrix (MPOTensor.physicalAdjointTensor U) N b =
      star (finiteChainMPOMatrix U N b) := by
  apply CStarMatrix.ext
  intro σ τ
  change MPOTensor.mpo (MPOTensor.physicalAdjointTensor U) N
    ((finiteChainConfigEquiv d N b).symm σ) ((finiteChainConfigEquiv d N b).symm τ) =
      star (MPOTensor.mpo U N ((finiteChainConfigEquiv d N b).symm τ)
        ((finiteChainConfigEquiv d N b).symm σ))
  exact MPOTensor.mpo_physicalAdjointTensor U N _ _

/-- Actual conjugation by the physical adjoint undoes actual original
MPU conjugation on the same finite chain.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem finiteChainConjugation_physicalAdjointTensor_apply_apply {d D : ℕ}
    {U : MPOTensor d D} (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (b : ℤ)
    (A : LocalAlgebra d (finiteChainRegion b N)) :
    finiteChainConjugation hU.physicalAdjointTensor hN b
      (finiteChainConjugation hU hN b A) = A := by
  have hunit := (finiteChainMPUUnitary hU hN b).property.1
  change star (finiteChainMPOMatrix U N b) * finiteChainMPOMatrix U N b = 1 at hunit
  simp only [finiteChainConjugation_apply, finiteChainMPOMatrix_physicalAdjointTensor,
    star_star, mul_assoc]
  rw [hunit, mul_one, ← mul_assoc, hunit, one_mul]

/-- Actual original MPU conjugation undoes actual physical-adjoint
conjugation on the same finite chain.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem finiteChainConjugation_apply_physicalAdjointTensor_apply {d D : ℕ}
    {U : MPOTensor d D} (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (b : ℤ)
    (A : LocalAlgebra d (finiteChainRegion b N)) :
    finiteChainConjugation hU hN b
      (finiteChainConjugation hU.physicalAdjointTensor hN b A) = A := by
  have hunit := (finiteChainMPUUnitary hU hN b).property.2
  change finiteChainMPOMatrix U N b * star (finiteChainMPOMatrix U N b) = 1 at hunit
  simp only [finiteChainConjugation_apply, finiteChainMPOMatrix_physicalAdjointTensor,
    star_star, mul_assoc]
  rw [hunit, mul_one, ← mul_assoc, hunit, one_mul]

/-- The actual physical-adjoint finite conjugation is the inverse
star-automorphism, rather than a supplied inverse-family assertion.
Source: arXiv:1703.09188, eq:appendix-1, lines 2300--2306. -/
theorem finiteChainConjugation_physicalAdjointTensor {d D : ℕ}
    {U : MPOTensor d D} (hU : U.IsMPU) {N : ℕ} (hN : 1 < N) (b : ℤ) :
    finiteChainConjugation hU.physicalAdjointTensor hN b =
      (finiteChainConjugation hU hN b).symm := by
  apply StarAlgEquiv.ext
  intro A
  have h := finiteChainConjugation_physicalAdjointTensor_apply_apply hU hN b
    ((finiteChainConjugation hU hN b).symm A)
  rw [StarAlgEquiv.apply_symm_apply] at h
  exact h

end SpinChain
