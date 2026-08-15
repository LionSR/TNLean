/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.CPSVBlocking
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.MPDO.RescalingStableLengthDependentRFPCanonicalForm
import TNLean.MPS.RFP.BNTOrthogonality

/-!
# Presentation-independent nonsimplicity of the rescaling-stable dimer tensor

The transfer map of the rescaling-stable dimer tensor `R` is quasi-idempotent
with scalar $337/512$. After blocking $L>0$ sites, the scalar is
$(337/512)^L$, which is strictly smaller than one. A normalized BNT horizontal
canonical form would force this scalar to equal one by its global unit-weight
copy and the trace-preserving normalization of that copy. Hence no positive
blocking of `R` has horizontal canonical form, independently of the chosen BNT
presentation, and `R` is not simple.

No vertical coefficient comparison is used.

## Main results

* `transferMap_blockTensor_R_toMPSTensor_quasi_idempotent` — the blocked
  transfer scalar is $(337/512)^L$.
* `blockTensor_R_not_isHorizontalCF` — no positive blocking admits a normalized
  BNT horizontal canonical form.
* `R_not_isSimple` — the dimer tensor is not simple.

The obstruction combines the source normalization at arXiv:1606.00608, line
246 with the positive blocking in the definition of simplicity at lines
815--822.
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPOTensor

variable {d D : ℕ}

/-- A normalized BNT-refined horizontal form forces the scalar in a transfer
quasi-idempotence equation to equal one.

The horizontal gauge transports the equation to the normalized sector
decomposition, where
`MPSTensor.IsBNTCanonicalForm.eq_one_of_transferMap_comp_self_eq_smul`
applies. -/
theorem IsHorizontalCF.eq_one_of_transferMap_comp_self_eq_smul
    {M : MPOTensor d D} (hHorizontal : IsHorizontalCF M) (c : ℂ)
    (h : MPSTensor.transferMap M.toMPSTensor ∘ₗ
        MPSTensor.transferMap M.toMPSTensor =
      c • MPSTensor.transferMap M.toMPSTensor) :
    c = 1 := by
  obtain ⟨S, hCF, hTotal, X, hEq⟩ := hHorizontal
  subst D
  have hGauge : MPSTensor.GaugeEquiv S.toTensor M.toMPSTensor := by
    refine ⟨MPSTensor.globalGaugeOfBlocks X, ?_⟩
    intro i
    simpa using hEq i
  have hSector := (hGauge.transferMap_comp_self_eq_smul_iff c).mp h
  exact hCF.eq_one_of_transferMap_comp_self_eq_smul S c hSector

end MPOTensor

namespace MPOTensor.RescalingStableLengthDependentRFP

/-- The transfer map of the $L$-site blocked dimer tensor is quasi-idempotent
with scalar $(337/512)^L$.

Project example; the blocking convention is arXiv:1606.00608, lines 815--822. -/
theorem transferMap_blockTensor_R_toMPSTensor_quasi_idempotent (L : ℕ) :
    MPSTensor.transferMap (MPOTensor.blockTensor R L).toMPSTensor *
        MPSTensor.transferMap (MPOTensor.blockTensor R L).toMPSTensor =
      (337/512 : ℂ) ^ L •
        MPSTensor.transferMap (MPOTensor.blockTensor R L).toMPSTensor := by
  rw [MPOTensor.toMPSTensor_blockTensor,
    MPSTensor.transferMap_reindexPhysical_equiv]
  apply MPSTensor.transferMap_blockTensor_quasi_idempotent
  apply LinearMap.ext
  intro X
  simpa only [Module.End.mul_apply, LinearMap.smul_apply] using
    transferMap_R_toMPSTensor_idem X

/-- No positive physical blocking of `R` admits a normalized BNT-refined
horizontal canonical form.

This conclusion is independent of the chosen BNT presentation: the proof uses
only the existence of a unit-weight copy in any normalized BNT witness, then
restricts transfer quasi-idempotence to that copy.

Source: arXiv:1606.00608, line 246 and lines 815--822. -/
theorem blockTensor_R_not_isHorizontalCF (L : ℕ) (hL : 0 < L) :
    ¬ MPOTensor.IsHorizontalCF (MPOTensor.blockTensor R L) := by
  intro hHorizontal
  have hBlocked := transferMap_blockTensor_R_toMPSTensor_quasi_idempotent L
  have hBlockedComp :
      MPSTensor.transferMap (MPOTensor.blockTensor R L).toMPSTensor ∘ₗ
          MPSTensor.transferMap (MPOTensor.blockTensor R L).toMPSTensor =
        (337/512 : ℂ) ^ L •
          MPSTensor.transferMap (MPOTensor.blockTensor R L).toMPSTensor := by
    simpa only [Module.End.mul_eq_comp] using hBlocked
  have hone := hHorizontal.eq_one_of_transferMap_comp_self_eq_smul
    ((337/512 : ℂ) ^ L) hBlockedComp
  have hlt : (337/512 : ℝ) ^ L < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hL)
  have hne : (337/512 : ℂ) ^ L ≠ 1 := by
    intro heq
    have hcast : (337/512 : ℂ) = ((337/512 : ℝ) : ℂ) := by norm_num
    rw [hcast] at heq
    have heqReal : (337/512 : ℝ) ^ L = 1 := by
      exact_mod_cast heq
    exact (ne_of_lt hlt) heqReal
  exact hne hone

/-- The rescaling-stable dimer tensor `R` is not simple, for every canonical-form
presentation and every positive blocking length.

Source: arXiv:1606.00608, definition of simplicity at lines 815--822. -/
theorem R_not_isSimple : ¬ MPOTensor.IsSimple R := by
  intro hSimple
  obtain ⟨_hMPDO, L, hL, hCanonical⟩ := hSimple
  exact blockTensor_R_not_isHorizontalCF L hL hCanonical.isHorizontalCF

end MPOTensor.RescalingStableLengthDependentRFP
