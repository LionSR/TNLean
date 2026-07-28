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
implication first applies the pure Perron gauge into canonical form II, uses the
left-canonical structural theorem there, and then returns through gauge
invariance. The reverse implication is the direct rank-one transfer-map
calculation.

The diagonal dressing in `IsIsometryCanonicalForm` is the documented
square-root correction to the source display: the decomposition uses
`Real.sqrt Λ`, while `Λ` itself is positive and trace-normalized.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- **Normal-tensor RFP/isometry characterization**
(arXiv:1606.00608, Lemma `charact-NT-pure-RFP`, lines 1274--1301).

For a positive-bond-dimension normal tensor, transfer-map idempotence is
equivalent to isometry canonical form. No external canonical-form-II or
left-canonical hypothesis is required: the forward implication obtains a
trace-preserving Perron gauge from normality, transports idempotence and
algebraic normality to that gauge, applies the left-canonical Appendix B
theorem, and transports the resulting structure back. The reverse implication
is `isTransferIdempotent_of_isIsometryCanonicalForm`.

The diagonal factor is `sqrt Λ`, with `Λ` positive and trace-normalized, as
explained in `IsIsometryCanonicalForm`. -/
theorem isTransferIdempotent_iff_isIsometryCanonicalForm_of_isNormalTensor
    (A : MPSTensor d D) [NeZero D] (hNT : IsNormalTensor A) :
    IsTransferIdempotent A ↔ IsIsometryCanonicalForm A := by
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
