/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.CanonicalFormEqual
import TNLean.MPS.SharedInfra.CoisometryGauge

/-!
# Equal-ambient fundamental theorem for CPSV canonical forms

This module lifts the active-core equal theorem to the original tensors when their ambient bond
spaces have the same dimension.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}
variable {A B : MPSTensor d D}

namespace CPSVCanonicalFormData

/-- **Equal-ambient CPSV fundamental theorem.**

Two normalized nonzero CPSV canonical-form tensors in the same ambient bond dimension that generate
the same matrix product vectors at every positive length are gauge equivalent. Inactive
zero-weight blocks and unused ambient coordinates are allowed: the exact active reconstructions
retain only the nonzero-weight blocks, while the ambient lifting aligns their possibly different
coisometric inclusions.

This theorem is explicitly homogeneous in the ambient dimension `D`; it makes no heterogeneous
ambient-dimension claim.

Source: arXiv:2011.12127v2, lines 1831--1906; arXiv:1606.00608, lines 237--301 and
1135--1199. -/
theorem fundamentalTheorem_equal_ambient_canonicalForm
    (dataA : CPSVCanonicalFormData A)
    (dataB : CPSVCanonicalFormData B)
    (hNormA : dataA.IsWeightNormalized)
    (hNormB : dataB.IsWeightNormalized)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hEqual : SameMPV₂Pos A B) :
    GaugeEquiv A B := by
  obtain ⟨P, hPBNT, _hPDim, UA, hUA, XA, hRecA⟩ :=
    dataA.exists_active_isBNTCanonicalForm_exact hNormA hA
  obtain ⟨Q, hQBNT, _hQDim, UB, hUB, XB, hRecB⟩ :=
    dataB.exists_active_isBNTCanonicalForm_exact hNormB hB
  let C : MPSTensor d P.totalDim := fun i =>
    (XA : Matrix _ _ ℂ) * P.toTensor i * (↑(XA⁻¹) : Matrix _ _ ℂ)
  let E : MPSTensor d Q.totalDim := fun i =>
    (XB : Matrix _ _ ℂ) * Q.toTensor i * (↑(XB⁻¹) : Matrix _ _ ℂ)
  have hAC : SameMPV₂Pos A C :=
    sameMPV₂Pos_of_coisometry_reconstruction A C UA hUA hRecA
  have hBE : SameMPV₂Pos B E :=
    sameMPV₂Pos_of_coisometry_reconstruction B E UB hUB hRecB
  have hPC : SameMPV₂Pos P.toTensor C :=
    fun N _hN w => GaugeEquiv.sameMPV ⟨XA, fun _ => rfl⟩ N w
  have hQE : SameMPV₂Pos Q.toTensor E :=
    fun N _hN w => GaugeEquiv.sameMPV ⟨XB, fun _ => rfl⟩ N w
  have hPQ : SameMPV₂Pos P.toTensor Q.toTensor :=
    hPC.trans (hAC.symm.trans (hEqual.trans (hBE.trans hQE.symm)))
  obtain ⟨hTotal, Y, hGauge⟩ :=
    fundamentalTheorem_equal_canonicalForm hPBNT hQBNT hPQ
  cases hTotal
  have hCE : GaugeEquiv C E := by
    exact (⟨XA, fun _ => rfl⟩ : GaugeEquiv P.toTensor C).symm.trans
      ((⟨Y, hGauge⟩ : GaugeEquiv P.toTensor Q.toTensor).trans
        (⟨XB, fun _ => rfl⟩ : GaugeEquiv Q.toTensor E))
  exact GaugeEquiv.of_coisometry_reconstruction UA UB hUA hUB hRecA hRecB hCE

end CPSVCanonicalFormData

end MPSTensor
