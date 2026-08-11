/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.CanonicalFormBridge
import TNLean.MPS.FundamentalTheorem.SectorBNT.FundamentalCoord

/-!
# Equal fundamental theorem for active CPSV canonical forms

Two normalized nonzero CPSV canonical-form tensors with equal positive-length matrix product
vectors determine active SectorBNT tensors of the same total bond dimension. The active tensors are
related by a single unitary gauge, and hence by an invertible gauge.

The conclusions concern the extracted active tensors. They make no assertion about equality of the
ambient bond dimensions or gauge equivalence of the original tensors.

Source: arXiv:2011.12127v2, lines 1831--1906; arXiv:1606.00608, lines 354--361 and
1172--1199.
-/
open scoped Matrix BigOperators

namespace MPSTensor

variable {d D₁ D₂ : ℕ}
variable {A : MPSTensor d D₁} {B : MPSTensor d D₂}

namespace CPSVCanonicalFormData

/-- **Active-core unitary equal fundamental theorem.**

Normalized nonzero CPSV canonical-form tensors with equal positive-length matrix product vectors
have active SectorBNT decompositions whose total dimensions agree. After identifying those active
dimensions, one unitary matrix conjugates the first extracted tensor to the second.

The common dimension is the sum of the dimensions of the nonzero-weight blocks. No equality of the
ambient bond dimensions, and no gauge equivalence between the original tensors, is asserted.

**Scope restriction (active canonical-form tensors):** This is the active-only corrected form of the
cited unitary theorem. It compares the extracted nonzero-weight SectorBNT tensors rather than the
literal ambient canonical forms. The restricted source interpretation is recorded in
`docs/paper-gaps/canonical_bnt_ft_theorem_surface.tex`.

Source: arXiv:2011.12127v2, lines 1831--1906, especially Corollary IV.5 and the unitary
note at lines 1905--1906; arXiv:1606.00608, lines 354--361 and 1172--1199. -/
theorem exists_active_fundamentalTheorem_equal_canonicalForm_unitary
    (dataA : CPSVCanonicalFormData A)
    (dataB : CPSVCanonicalFormData B)
    (hNormA : dataA.IsWeightNormalized)
    (hNormB : dataB.IsWeightNormalized)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hEqual : SameMPV₂Pos A B) :
    ∃ P Q : SectorDecomposition d,
      IsBNTCanonicalForm P ∧
      IsBNTCanonicalForm Q ∧
      SameMPV₂Pos A P.toTensor ∧
      SameMPV₂Pos B Q.toTensor ∧
      P.totalDim = ∑ k : dataA.Active, dataA.dim k.1 ∧
      Q.totalDim = ∑ k : dataB.Active, dataB.dim k.1 ∧
      (∑ k : dataA.Active, dataA.dim k.1) =
        ∑ k : dataB.Active, dataB.dim k.1 ∧
      ∃ (hTotal : P.totalDim = Q.totalDim)
          (Y : GL (Fin Q.totalDim) ℂ),
        (Y : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) ∈
          Matrix.unitaryGroup (Fin Q.totalDim) ℂ ∧
        ∀ i : Fin d,
          Q.toTensor i =
            (Y : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
              cast (by rw [hTotal] :
                  Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
                  Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)
                (P.toTensor i) *
              (((Y)⁻¹ : GL (Fin Q.totalDim) ℂ) :
                Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) := by
  obtain ⟨P, hPBNT, hAP, hPDim⟩ :=
    dataA.exists_active_isBNTCanonicalForm hNormA hA
  obtain ⟨Q, hQBNT, hBQ, hQDim⟩ :=
    dataB.exists_active_isBNTCanonicalForm hNormB hB
  have hPQ : SameMPV₂Pos P.toTensor Q.toTensor :=
    hAP.symm.trans (hEqual.trans hBQ)
  obtain ⟨hTotal, Y, hYUnitary, hGauge⟩ :=
    fundamentalTheorem_equal_canonicalForm_unitary hPBNT hQBNT hPQ
  have hActiveTotal :
      (∑ k : dataA.Active, dataA.dim k.1) =
        ∑ k : dataB.Active, dataB.dim k.1 :=
    hPDim.symm.trans (hTotal.trans hQDim)
  exact ⟨P, Q, hPBNT, hQBNT, hAP, hBQ, hPDim, hQDim, hActiveTotal,
    hTotal, Y, hYUnitary, hGauge⟩

/-- **Active-core equal fundamental theorem.**

Normalized nonzero CPSV canonical-form tensors with equal positive-length matrix product vectors
have active SectorBNT decompositions of equal total dimension, related by one invertible global
gauge. This follows from the unitary active-core theorem by forgetting unitarity.

The theorem concerns only the extracted nonzero-weight blocks. It does not identify the ambient bond
dimensions and does not claim gauge equivalence of the original tensors.

**Scope restriction (active canonical-form tensors):** This is the active-only corrected form of the
cited equal fundamental theorem. It compares the extracted nonzero-weight SectorBNT tensors rather
than the literal ambient canonical forms. The restricted source interpretation is recorded in
`docs/paper-gaps/canonical_bnt_ft_theorem_surface.tex`.

Source: arXiv:2011.12127v2, lines 1831--1900, especially Corollary IV.5;
arXiv:1606.00608, lines 354--361 and 1172--1192. -/
theorem exists_active_fundamentalTheorem_equal_canonicalForm
    (dataA : CPSVCanonicalFormData A)
    (dataB : CPSVCanonicalFormData B)
    (hNormA : dataA.IsWeightNormalized)
    (hNormB : dataB.IsWeightNormalized)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hEqual : SameMPV₂Pos A B) :
    ∃ P Q : SectorDecomposition d,
      IsBNTCanonicalForm P ∧
      IsBNTCanonicalForm Q ∧
      SameMPV₂Pos A P.toTensor ∧
      SameMPV₂Pos B Q.toTensor ∧
      P.totalDim = ∑ k : dataA.Active, dataA.dim k.1 ∧
      Q.totalDim = ∑ k : dataB.Active, dataB.dim k.1 ∧
      (∑ k : dataA.Active, dataA.dim k.1) =
        ∑ k : dataB.Active, dataB.dim k.1 ∧
      ∃ (hTotal : P.totalDim = Q.totalDim)
          (Y : GL (Fin Q.totalDim) ℂ),
        ∀ i : Fin d,
          Q.toTensor i =
            (Y : Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) *
              cast (by rw [hTotal] :
                  Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
                  Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ)
                (P.toTensor i) *
              (((Y)⁻¹ : GL (Fin Q.totalDim) ℂ) :
                Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) := by
  obtain ⟨P, Q, hPBNT, hQBNT, hAP, hBQ, hPDim, hQDim, hActiveTotal,
      hTotal, Y, _hYUnitary, hGauge⟩ :=
    dataA.exists_active_fundamentalTheorem_equal_canonicalForm_unitary
      dataB hNormA hNormB hA hB hEqual
  exact ⟨P, Q, hPBNT, hQBNT, hAP, hBQ, hPDim, hQDim, hActiveTotal,
    hTotal, Y, hGauge⟩

end CPSVCanonicalFormData

end MPSTensor
