/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.AreaLaw
import TNLean.MPS.MPDO.SimpleScaling

/-!
# Saturation of the area law under positive rescaling

Block entropies and mutual informations of an MPO tensor depend only on its
normalized density-operator family, which is unchanged by a nonzero complex
rescaling of the tensor. Saturation of the area law (CPSV16 Definition 4.6)
additionally asks for the MPDO condition and nonzero positive-length traces;
both survive a strictly positive real rescaling. Hence saturation of the area
law is invariant under multiplication by a strictly positive real scalar.

## Main results

* `MPOTensor.reducedBlockState_smul`, `MPOTensor.blockEntropy_smul`,
  `MPOTensor.mutualInfoChain_smul`: reduced block states, block entropies, and
  mutual informations are unchanged by nonzero complex rescaling.
* `MPOTensor.isSAL_smul_ofReal_iff`: saturation of the area law is invariant
  under strictly positive real rescaling.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608, Definition 4.6,
  lines 811--815, and the normalization convention of line 792.
-/

open scoped ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- Rescaling the tensor by a nonzero complex scalar leaves every reduced block
state unchanged.

Project-derived from the normalization convention of arXiv:1606.00608,
line 792. -/
theorem reducedBlockState_smul {c : ℂ} (hc : c ≠ 0) (M : MPOTensor d D)
    (N L : ℕ) (hL : L ≤ N) :
    reducedBlockState (c • M) N L hL = reducedBlockState M N L hL := by
  simp only [reducedBlockState, normalizedMPO_smul hc]

/-- Rescaling the tensor by a nonzero complex scalar leaves every block entropy
unchanged. The positivity witnesses of the two closed operators are independent.

Project-derived from arXiv:1606.00608, line 797, and the normalization
convention of line 792. -/
theorem blockEntropy_smul {c : ℂ} (hc : c ≠ 0) (M : MPOTensor d D) (N L : ℕ)
    (hL : L ≤ N) (h₁ : (mpo (c • M) N).PosSemidef) (h₂ : (mpo M N).PosSemidef) :
    blockEntropy (c • M) N L hL h₁ = blockEntropy M N L hL h₂ :=
  vonNeumannEntropy_congr (reducedBlockState_smul hc M N L hL) _ _

/-- Rescaling the tensor by a nonzero complex scalar leaves every mutual
information `I_L` unchanged.

Project-derived from arXiv:1606.00608, line 797, and the normalization
convention of line 792. -/
theorem mutualInfoChain_smul {c : ℂ} (hc : c ≠ 0) (M : MPOTensor d D) (N L : ℕ)
    (hL : L ≤ N) (h₁ : (mpo (c • M) N).PosSemidef) (h₂ : (mpo M N).PosSemidef) :
    mutualInfoChain (c • M) N L hL h₁ = mutualInfoChain M N L hL h₂ := by
  simp only [mutualInfoChain, blockEntropy_smul hc M N _ _ h₁ h₂]

/-- Saturation of the area law is invariant under multiplication by a strictly
positive real scalar.

Project-derived from arXiv:1606.00608, Definition 4.6, lines 811--815: the
mutual informations depend only on the normalized states, the MPDO condition
is invariant under positive rescaling, and the length-`N` trace is multiplied
by the nonzero factor `r ^ N`. -/
theorem isSAL_smul_ofReal_iff (M : MPOTensor d D) {r : ℝ} (hr : 0 < r) :
    IsSAL ((r : ℂ) • M) ↔ IsSAL M := by
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have htr : ∀ N, (mpo ((r : ℂ) • M) N).trace ≠ 0 ↔ (mpo M N).trace ≠ 0 := by
    intro N
    rw [mpo_smul, Matrix.trace_smul, smul_eq_mul, mul_ne_zero_iff,
      and_iff_right (pow_ne_zero N hc)]
  constructor
  · rintro ⟨hMpdo, htrace, hmi⟩
    have hM := (isMPDO_smul_ofReal_iff M hr).1 hMpdo
    refine ⟨hM, fun N hN ↦ (htr N).1 (htrace N hN), fun N L h1 hL ↦ ?_⟩
    rw [← mutualInfoChain_smul hc M N L _ (hMpdo N (by omega)),
      ← mutualInfoChain_smul hc M N (L + 1) _ (hMpdo N (by omega))]
    exact hmi N L h1 hL
  · rintro ⟨hM, htrace, hmi⟩
    have hMpdo := (isMPDO_smul_ofReal_iff M hr).2 hM
    refine ⟨hMpdo, fun N hN ↦ (htr N).2 (htrace N hN), fun N L h1 hL ↦ ?_⟩
    rw [mutualInfoChain_smul hc M N L _ _ (hM N (by omega)),
      mutualInfoChain_smul hc M N (L + 1) _ _ (hM N (by omega))]
    exact hmi N L h1 hL

end MPOTensor
