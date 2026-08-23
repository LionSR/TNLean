/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Core.BlockingTransfer
import TNLean.MPS.MPDO.RescalingStableSourceSimple
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
* `R_not_isSimple` — the dimer tensor is not simple for the normalized
  fixed-representative predicate.
* `R_isSourceSimple_and_not_isSimple` — the canonical-block reading of
  Definition 4.7 and the normalized fixed-representative verdict side by side.

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
    (h : Kraus.transferMap M.toMPSTensor ∘ₗ
        Kraus.transferMap M.toMPSTensor =
      c • Kraus.transferMap M.toMPSTensor) :
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

Project example; the physical blocking convention is arXiv:1606.00608,
lines 227--231. -/
theorem transferMap_blockTensor_R_toMPSTensor_quasi_idempotent (L : ℕ) :
    Kraus.transferMap (MPOTensor.blockTensor R L).toMPSTensor *
        Kraus.transferMap (MPOTensor.blockTensor R L).toMPSTensor =
      (337/512 : ℂ) ^ L •
        Kraus.transferMap (MPOTensor.blockTensor R L).toMPSTensor := by
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

**Scope restriction (BNT-refined horizontal form):** `IsHorizontalCF` is the
project's BNT-refined exact-gauge predicate, which is stronger than literal CPSV
canonical form. See `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, line 246 and lines 815--822. -/
theorem blockTensor_R_not_isHorizontalCF (L : ℕ) (hL : 0 < L) :
    ¬ MPOTensor.IsHorizontalCF (MPOTensor.blockTensor R L) := by
  intro hHorizontal
  have hBlocked := transferMap_blockTensor_R_toMPSTensor_quasi_idempotent L
  have hBlockedComp :
      Kraus.transferMap (MPOTensor.blockTensor R L).toMPSTensor ∘ₗ
          Kraus.transferMap (MPOTensor.blockTensor R L).toMPSTensor =
        (337/512 : ℂ) ^ L •
          Kraus.transferMap (MPOTensor.blockTensor R L).toMPSTensor := by
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

**Scope restriction (fixed representative):** This theorem concerns the current
normalized-witness predicate `MPOTensor.IsSimple`, not a scale-invariant notion
of simplicity. See `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`.

Source: arXiv:1606.00608, definition of simplicity at lines 815--822. -/
theorem R_not_isSimple : ¬ MPOTensor.IsSimple R := by
  intro hSimple
  obtain ⟨_hMPDO, L, hL, hCanonical⟩ := hSimple
  exact blockTensor_R_not_isHorizontalCF L hL hCanonical.isHorizontalCF

/-- The dimer tensor receives opposite verdicts from the two simplicity predicates: it
satisfies the canonical-block reading of Definition 4.7, while it fails the normalized
fixed-representative predicate `MPOTensor.IsSimple`.

The first verdict uses the existential one-site BNT presentation and does not assert
simplicity at every positive blocking. The second is the line-246 normalization obstruction
proved by `R_not_isSimple`.

Source: arXiv:1606.00608, line 246 and Definition 4.7, lines 815--822. -/
@[deprecated "Use `R_isSourceSimple` and `R_not_isSimple` directly."
  (since := "2026-08-15")]
theorem R_isSourceSimple_and_not_isSimple :
    MPOTensor.IsSourceSimple R ∧ ¬ MPOTensor.IsSimple R :=
  ⟨R_isSourceSimple, R_not_isSimple⟩

end MPOTensor.RescalingStableLengthDependentRFP
