/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.CanonicalFormBridge
import TNLean.MPS.FundamentalTheorem.SectorBNT.FundamentalCoord
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

private lemma mpsTensor_cast_apply {n m : ℕ} (h : n = m)
    (T : MPSTensor d n) (i : Fin d) :
    (cast (congr_arg (MPSTensor d) h) T) i =
      cast (congr_arg (fun r => Matrix (Fin r) (Fin r) ℂ) h) (T i) := by
  subst h
  rfl

private lemma coisometry_cast_rows {n m : ℕ} (h : n = m)
    (U : Matrix (Fin n) (Fin D) ℂ) (hU : U * Uᴴ = 1) :
    let V := cast (congr_arg (fun r => Matrix (Fin r) (Fin D) ℂ) h) U
    V * Vᴴ = 1 := by
  subst h
  exact hU

private lemma reconstruction_cast_rows {n m : ℕ} (h : n = m)
    (T : MPSTensor d n) (U : Matrix (Fin n) (Fin D) ℂ)
    (hRec : ∀ i, A i = Uᴴ * T i * U) :
    let T' := cast (congr_arg (MPSTensor d) h) T
    let U' := cast (congr_arg (fun r => Matrix (Fin r) (Fin D) ℂ) h) U
    ∀ i, A i = U'ᴴ * T' i * U' := by
  subst h
  exact hRec

private lemma gaugeEquiv_cast_dim {n m : ℕ} (h : n = m)
    {S T : MPSTensor d n} (hGauge : GaugeEquiv S T) :
    GaugeEquiv (cast (congr_arg (MPSTensor d) h) S)
      (cast (congr_arg (MPSTensor d) h) T) := by
  subst h
  exact hGauge

/-- **Equal-ambient CPSV fundamental theorem.**

Two normalized nonzero CPSV canonical-form tensors in the same ambient bond
dimension that generate the same matrix product vectors at every positive length
are gauge equivalent. Inactive zero-weight blocks and unused ambient coordinates
are allowed: the exact active reconstructions retain only the nonzero-weight blocks,
while the ambient lifting aligns their possibly different coisometric inclusions.

This theorem is explicitly homogeneous in the ambient dimension \(D\); it makes no
heterogeneous ambient-dimension claim. The ambient lifting is a project-derived
corollary of the cited active fundamental theorem and the coisometry-alignment lemma.

**Scope restriction (equal ambient dimension and nonzero tensors):** The theorem
assumes a common ambient bond dimension and excludes zero tensors. It does not prove
the heterogeneous ambient statement of the cited source corollary. See
`docs/paper-gaps/tnlean_bnt_ft_theorem_surface.tex`.

Source: arXiv:2011.12127v2, lines 1831--1906; arXiv:1606.00608,
lines 237--301 and 1135--1199. -/
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
  have hGaugePC : GaugeEquiv P.toTensor C := ⟨XA, fun _ => rfl⟩
  have hGaugeQE : GaugeEquiv Q.toTensor E := ⟨XB, fun _ => rfl⟩
  have hAC : SameMPV₂Pos A C :=
    sameMPV₂Pos_of_coisometry_reconstruction A C UA hUA hRecA
  have hBE : SameMPV₂Pos B E :=
    sameMPV₂Pos_of_coisometry_reconstruction B E UB hUB hRecB
  have hPC : SameMPV₂Pos P.toTensor C :=
    fun N _hN w => GaugeEquiv.sameMPV hGaugePC N w
  have hQE : SameMPV₂Pos Q.toTensor E :=
    fun N _hN w => GaugeEquiv.sameMPV hGaugeQE N w
  have hPQ : SameMPV₂Pos P.toTensor Q.toTensor :=
    hPC.trans (hAC.symm.trans (hEqual.trans (hBE.trans hQE.symm)))
  obtain ⟨hTotal, Y, hGauge⟩ :=
    fundamentalTheorem_equal_canonicalForm hPBNT hQBNT hPQ
  let P' := cast (congr_arg (MPSTensor d) hTotal) P.toTensor
  let C' := cast (congr_arg (MPSTensor d) hTotal) C
  let UA' := cast
    (congr_arg (fun r => Matrix (Fin r) (Fin D) ℂ) hTotal) UA
  have hP'Q : GaugeEquiv P' Q.toTensor := by
    refine ⟨Y, fun i => ?_⟩
    have hPi : P' i =
        cast (by rw [hTotal] :
          Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
            Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ) (P.toTensor i) := by
      let hm : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ =
          Matrix (Fin Q.totalDim) (Fin Q.totalDim) ℂ := by rw [hTotal]
      have hp : congr_arg (fun r => Matrix (Fin r) (Fin r) ℂ) hTotal = hm :=
        Subsingleton.elim _ _
      calc
        P' i = cast (congr_arg (fun r => Matrix (Fin r) (Fin r) ℂ) hTotal)
            (P.toTensor i) := mpsTensor_cast_apply hTotal P.toTensor i
        _ = cast hm (P.toTensor i) := by rw [hp]
    rw [hPi]
    exact hGauge i
  have hP'C' : GaugeEquiv P' C' :=
    gaugeEquiv_cast_dim hTotal hGaugePC
  have hCE : GaugeEquiv C' E :=
    hP'C'.symm.trans (hP'Q.trans hGaugeQE)
  have hUA' : UA' * UA'ᴴ = 1 :=
    coisometry_cast_rows hTotal UA hUA
  have hRecA' : ∀ i, A i = UA'ᴴ * C' i * UA' :=
    reconstruction_cast_rows hTotal C UA hRecA
  exact GaugeEquiv.of_coisometry_reconstruction
    UA' UB hUA' hUB hRecA' hRecB hCE

end CPSVCanonicalFormData

end MPSTensor
