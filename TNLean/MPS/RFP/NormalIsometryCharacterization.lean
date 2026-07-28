/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.RFP.StructuralFull

/-!
# Isometry characterization of normal renormalization fixed points

A spectrally normal tensor is a renormalization fixed point exactly when it has
the single-block isometry form from Appendix B of arXiv:1606.00608. The forward
implication first passes to its left-canonical, trace-preserving Perron
representative, uses the structural theorem there, and then returns through
gauge invariance. The reverse implication is the direct rank-one transfer-map
calculation.

The diagonal dressing in `IsIsometryCanonicalForm` is the documented
square-root correction to the source display: the decomposition uses
`Real.sqrt Λ`, while `Λ` itself is positive and trace-normalized.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- **Normal-tensor RFP/isometry characterization**
(arXiv:1606.00608, Lemma `charact-NT-pure-RFP`, lines 1274--1301).

For a normal tensor, transfer-map idempotence is equivalent to isometry
canonical form. Normality itself forces positive bond dimension, so no
external bond-dimension or left-canonical hypothesis is required. The forward
implication obtains a left-canonical, trace-preserving Perron representative
from normality, carries idempotence and algebraic normality to that
representative, applies the Appendix B theorem, and carries the resulting
structure back. The reverse implication is
`isTransferIdempotent_of_isIsometryCanonicalForm`.

**Local fix (square-root diagonal):** the diagonal factor is `sqrt Λ`, with `Λ`
positive and trace-normalized, rather than the bare `Λ` in the source display.
This correction is documented in
`docs/paper-gaps/cpsv16_rfp_isometry_scope.tex`. -/
theorem IsNormalTensor.isTransferIdempotent_iff_isIsometryCanonicalForm
    {A : MPSTensor d D} (hNT : IsNormalTensor A) :
    IsTransferIdempotent A ↔ IsIsometryCanonicalForm A := by
  letI : NeZero D := ⟨hNT.bondDim_ne_zero⟩
  constructor
  · intro hRFP
    obtain ⟨σ, _hσ, _hσfix, hLeft, hGauge, _hPrim, _hIrr⟩ := hNT.exists_tpGauge
    have hRFP' : IsTransferIdempotent (tpGauge (d := d) (D := D) A σ) :=
      hGauge.isTransferIdempotent_iff.mp hRFP
    have hNormal' : IsNormal (tpGauge (d := d) (D := D) A σ) :=
      isNormal_of_gaugeEquiv hNT.isNormal hGauge
    have hIso' : IsIsometryCanonicalForm (tpGauge (d := d) (D := D) A σ) :=
      isIsometryCanonicalForm_of_rfp_nt _ hNormal' hRFP' hLeft
    exact hGauge.isIsometryCanonicalForm_iff.mpr hIso'
  · exact isTransferIdempotent_of_isIsometryCanonicalForm A

end MPSTensor
