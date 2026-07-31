/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrobeniusHilbert
import TNLean.Algebra.MatrixCongruence
import TNLean.Algebra.RectangularChoi
import TNLean.Channel.KrausCPTP
import TNLean.Channel.Peripheral.UnitalKraus

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Weighted Hilbert--Schmidt channel maps

This file develops the finite-dimensional Hilbert-space infrastructure and
proves the direct `p = 2` specialization of Beigi's weighted Schatten-norm
contraction. It also identifies the trace-pairing adjoint of a rectangular
Kraus map with its Hilbert-space adjoint after Frobenius vectorization.

## Main result

* `Matrix.adjoint_frobeniusEuclideanMap_eq`: the Hilbert-space adjoint of a
  Kraus map is its trace-pairing adjoint.
* `Matrix.weightedHilbertSchmidtMap`: the full-support weighted channel map.
* `Matrix.weightedHilbertSchmidtMap_norm_le`: its Hilbert--Schmidt contraction bound.

## References

* S. Beigi, *Sandwiched Rényi Divergence Satisfies Data Processing
  Inequality*, J. Math. Phys. 54 (2013), 122202, arXiv:1306.5920,
  Theorem 6 and equation (18).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius NNReal ENNReal

namespace Matrix

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-- After Frobenius vectorization, the Hilbert-space adjoint of a rectangular
Kraus map is its trace-pairing adjoint.

This is the adjoint identity used in the direct `p = 2` proof of Beigi,
arXiv:1306.5920, Theorem 6, equation (18). -/
theorem adjoint_frobeniusEuclideanMap_eq
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (hE : IsKrausCP E) :
    (frobeniusEuclideanMap E).adjoint =
      frobeniusEuclideanMap (traceAdjointMap E) := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro X Y
  rw [← (frobeniusEquivEuclidean β β).apply_symm_apply X,
    ← (frobeniusEquivEuclidean α α).apply_symm_apply Y]
  simp only [frobeniusEuclideanMap_apply, inner_frobeniusEquivEuclidean]
  have hstar (Z : Matrix β β ℂ) :
      (traceAdjointMap E Z)ᴴ = traceAdjointMap E Zᴴ := by
    obtain ⟨r, A, hA⟩ := hE.traceAdjointMap
    rw [hA, hA]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hstar, trace_traceAdjointMap_mul]

/-- The weighted channel map
`X ↦ τ^{-1/4} Φ(σ^{1/4} X σ^{1/4}) τ^{-1/4}` used in the full-support `p = 2`
specialization of Beigi, arXiv:1306.5920, Theorem 6, equation (18).

Invertibility of the two weights is imposed by the contraction theorem below. -/
noncomputable def weightedHilbertSchmidtMap
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (σ : Matrix α α ℂ) (τ : Matrix β β ℂ) :
    Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ :=
  (singleKrausMap (CFC.sqrt (CFC.sqrt τ))⁻¹).comp
    (Φ.comp (singleKrausMap (CFC.sqrt (CFC.sqrt σ))))

private theorem norm_apply_le_of_spectralRadius_adjoint_comp_le_one
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (L : V →L[ℂ] W)
    (hRad : spectralRadius ℂ (L.adjoint.comp L) ≤ 1) (x : V) :
    ‖L x‖ ≤ ‖x‖ := by
  let G := L.adjoint.comp L
  have hGsa : IsSelfAdjoint G := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    simp [G]
  have hGnorm : ‖G‖ ≤ 1 := by
    have hGnnorm : ‖G‖₊ ≤ 1 := by
      have hGenn : (↑‖G‖₊ : ENNReal) ≤ 1 := by
        rw [← G.spectralRadius_eq_nnnorm hGsa]
        exact hRad
      exact_mod_cast hGenn
    exact_mod_cast hGnnorm
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_adjoint_comp_self] at hGnorm
    nlinarith [norm_nonneg L]
  exact (L.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg x) hLnorm)

/-- The full-support `p = 2` specialization of the weighted Schatten-norm
contraction in Beigi, arXiv:1306.5920, Theorem 6, equation (18).

**Scope restriction (full output support):** The output weight is assumed
positive definite. The support-compressed form needed for arbitrary output
support is recorded in
`docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex`. -/
theorem weightedHilbertSchmidtMap_norm_le
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {σ : Matrix α α ℂ} {τ : Matrix β β ℂ}
    (hΦ : IsKrausCPTP Φ) (hσ : σ.PosDef) (hτ : τ.PosDef)
    (hmap : Φ σ = τ) (X : Matrix α α ℂ) :
    ‖weightedHilbertSchmidtMap Φ σ τ X‖ ≤ ‖X‖ := by
  let sσ := CFC.sqrt σ
  let qσ := CFC.sqrt sσ
  let sτ := CFC.sqrt τ
  let qτ := CFC.sqrt sτ
  have hsσ_psd : sσ.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)
  have hqσ_psd : qσ.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg sσ)
  have hsτ_psd : sτ.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg τ)
  have hqτ_psd : qτ.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg sτ)
  have hsσ_sq : sσ * sσ = σ := by
    simpa only [sσ] using CFC.sqrt_mul_sqrt_self σ hσ.posSemidef.nonneg
  have hqσ_sq : qσ * qσ = sσ := by
    simpa only [qσ] using CFC.sqrt_mul_sqrt_self sσ hsσ_psd.nonneg
  have hsτ_sq : sτ * sτ = τ := by
    simpa only [sτ] using CFC.sqrt_mul_sqrt_self τ hτ.posSemidef.nonneg
  have hqτ_sq : qτ * qτ = sτ := by
    simpa only [qτ] using CFC.sqrt_mul_sqrt_self sτ hsτ_psd.nonneg
  have hsσ_star : sσᴴ = sσ := by
    exact hsσ_psd.isHermitian
  have hqσ_star : qσᴴ = qσ := by
    exact hqσ_psd.isHermitian
  have hsτ_star : sτᴴ = sτ := by
    exact hsτ_psd.isHermitian
  have hqτ_star : qτᴴ = qτ := by
    exact hqτ_psd.isHermitian
  have hsσ_unit : IsUnit sσ :=
    (CFC.isUnit_sqrt_iff σ hσ.posSemidef.nonneg).2 hσ.isUnit
  have hqσ_unit : IsUnit qσ :=
    (CFC.isUnit_sqrt_iff sσ hsσ_psd.nonneg).2 hsσ_unit
  have hsτ_unit : IsUnit sτ :=
    (CFC.isUnit_sqrt_iff τ hτ.posSemidef.nonneg).2 hτ.isUnit
  have hqσ_det : qσ.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det qσ).1 hqσ_unit).ne_zero
  have hsτ_det_unit : IsUnit sτ.det :=
    (Matrix.isUnit_iff_isUnit_det sτ).1 hsτ_unit
  have hsτ_inv_star : (sτ⁻¹)ᴴ = sτ⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hsτ_star]
  have hsigma_one : singleKrausMap sσ 1 = σ := by
    rw [singleKrausMap_apply, hsσ_star, Matrix.mul_one, hsσ_sq]
  have htau_inv : singleKrausMap sτ⁻¹ τ = 1 := by
    rw [singleKrausMap_apply, hsτ_inv_star, ← hsτ_sq]
    calc
      sτ⁻¹ * (sτ * sτ) * sτ⁻¹ = (sτ⁻¹ * sτ) * (sτ * sτ⁻¹) := by
        noncomm_ring
      _ = 1 * 1 := by
        rw [Matrix.nonsing_inv_mul sτ hsτ_det_unit,
          Matrix.mul_nonsing_inv sτ hsτ_det_unit]
      _ = 1 := mul_one 1
  let E := (traceAdjointMap Φ).comp
    ((singleKrausMap sτ⁻¹).comp (Φ.comp (singleKrausMap sσ)))
  have hEcp : IsKrausCP E := by
    exact isKrausCP_comp
      (isKrausCP_comp
        (isKrausCP_comp (singleKrausMap_isKrausCP sσ) hΦ.isKrausCP)
        (singleKrausMap_isKrausCP sτ⁻¹))
      hΦ.isKrausCP.traceAdjointMap
  have hEone : E 1 = 1 := by
    simp only [E, LinearMap.comp_apply, hsigma_one, hmap, htau_inv]
    exact hΦ.traceAdjointMap_one
  let L := weightedHilbertSchmidtMap Φ σ τ
  let S := congruenceLinearEquiv qσ hqσ_det
  have hqτ_inv_sq : qτ⁻¹ * qτ⁻¹ = sτ⁻¹ := by
    rw [← Matrix.mul_inv_rev, hqτ_sq]
  have hqσ_inv_mul : qσ⁻¹ * qσ = 1 :=
    Matrix.nonsing_inv_mul qσ (Ne.isUnit hqσ_det)
  have hqσ_mul_inv : qσ * qσ⁻¹ = 1 :=
    Matrix.mul_nonsing_inv qσ (Ne.isUnit hqσ_det)
  have hAdjL : traceAdjointMap L =
      (singleKrausMap qσ).comp
        ((traceAdjointMap Φ).comp (singleKrausMap qτ⁻¹)) := by
    dsimp only [L, weightedHilbertSchmidtMap]
    rw [traceAdjointMap_comp, traceAdjointMap_comp,
      traceAdjointMap_singleKrausMap, traceAdjointMap_singleKrausMap]
    rw [Matrix.conjTranspose_nonsing_inv, hqτ_star, hqσ_star]
    rfl
  have hGramTrace : (traceAdjointMap L).comp L = S.conj E := by
    apply LinearMap.ext
    intro Y
    rw [LinearEquiv.conj_apply]
    change (traceAdjointMap L) (L Y) = S (E (S.symm Y))
    rw [hAdjL]
    rw [show S (E (S.symm Y)) = qσ * E (S.symm Y) * qσᴴ by
      exact congruenceLinearEquiv_apply qσ hqσ_det (E (S.symm Y))]
    rw [show S.symm Y = qσ⁻¹ * Y * (qσᴴ)⁻¹ by
      exact congruenceLinearEquiv_symm_apply qσ hqσ_det Y]
    simp only [L, weightedHilbertSchmidtMap, LinearMap.comp_apply,
      singleKrausMap_apply, E]
    rw [Matrix.conjTranspose_nonsing_inv, hqσ_star, hqτ_star, hsσ_star]
    have hInput : sσ * (qσ⁻¹ * Y * qσ⁻¹) * sσ = qσ * Y * qσ := by
      rw [← hqσ_sq]
      calc
        (qσ * qσ) * (qσ⁻¹ * Y * qσ⁻¹) * (qσ * qσ) =
            qσ * (qσ * qσ⁻¹) * Y * (qσ⁻¹ * qσ) * qσ := by
          noncomm_ring
        _ = qσ * Y * qσ := by rw [hqσ_mul_inv, hqσ_inv_mul]; simp
    have hOutput (Z : Matrix β β ℂ) :
        qτ⁻¹ * (qτ⁻¹ * Z * qτ⁻¹) * qτ⁻¹ = sτ⁻¹ * Z * sτ⁻¹ := by
      rw [← hqτ_inv_sq]
      noncomm_ring
    rw [hInput, hOutput]
    rw [hsτ_inv_star]
  have hLcp : IsKrausCP L := by
    exact isKrausCP_comp
      (isKrausCP_comp (singleKrausMap_isKrausCP qσ) hΦ.isKrausCP)
      (singleKrausMap_isKrausCP qτ⁻¹)
  let A := frobeniusEuclideanMap L
  let T := frobeniusEuclideanLinearEquiv S
  have hGramFrob : A.adjoint.comp A = T.conj (frobeniusEuclideanMap E) := by
    dsimp only [A, T]
    rw [adjoint_frobeniusEuclideanMap_eq L hLcp,
      ← frobeniusEuclideanMap_comp, hGramTrace, frobeniusEuclideanMap_conj]
  let V := EuclideanSpace ℂ (α × α)
  let Acl : EuclideanSpace ℂ (α × α) →L[ℂ] EuclideanSpace ℂ (β × β) :=
    LinearMap.toContinuousLinearMap A
  let Ψ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) :=
    Module.End.toContinuousLinearMap V
  have hGramCLM : Acl.adjoint.comp Acl = Ψ (T.conj (frobeniusEuclideanMap E)) := by
    apply ContinuousLinearMap.ext
    intro x
    change A.adjoint (A x) = (T.conj (frobeniusEuclideanMap E)) x
    exact DFunLike.congr_fun hGramFrob x
  have hSpecLeft :
      spectrum ℂ (Ψ (T.conj (frobeniusEuclideanMap E))) =
        spectrum ℂ (T.conj (frobeniusEuclideanMap E)) :=
    AlgEquiv.spectrum_eq Ψ (T.conj (frobeniusEuclideanMap E))
  have hSpecConj :
      spectrum ℂ (T.conj (frobeniusEuclideanMap E)) =
        spectrum ℂ (frobeniusEuclideanMap E) :=
    AlgEquiv.spectrum_eq (T.conjAlgEquiv ℂ) (frobeniusEuclideanMap E)
  have hSpecRight :
      spectrum ℂ (Ψ (frobeniusEuclideanMap E)) =
        spectrum ℂ (frobeniusEuclideanMap E) :=
    AlgEquiv.spectrum_eq Ψ (frobeniusEuclideanMap E)
  have hRadConj :
      spectralRadius ℂ (Ψ (T.conj (frobeniusEuclideanMap E))) =
        spectralRadius ℂ (Ψ (frobeniusEuclideanMap E)) := by
    rw [spectralRadius, spectralRadius, hSpecLeft, hSpecConj, hSpecRight]
  have hRadE : spectralRadius ℂ (Ψ (frobeniusEuclideanMap E)) ≤ 1 :=
    hEcp.spectralRadius_frobeniusEuclideanMap_le_one_of_map_one_eq_one hEone
  have hRadGram : spectralRadius ℂ (Acl.adjoint.comp Acl) ≤ 1 := by
    rw [hGramCLM, hRadConj]
    exact hRadE
  have hAx := norm_apply_le_of_spectralRadius_adjoint_comp_le_one Acl hRadGram
    (frobeniusEquivEuclidean α α X)
  simpa only [Acl, LinearMap.coe_toContinuousLinearMap', A,
    frobeniusEuclideanMap_apply, LinearIsometryEquiv.norm_map] using hAx

/-- The full-support weighted channel map is a Hilbert--Schmidt contraction.

This is the quadratic-form formulation of
`weightedHilbertSchmidtMap_norm_le`. -/
theorem weightedHilbertSchmidtMap_isHilbertSchmidtContraction
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {σ : Matrix α α ℂ} {τ : Matrix β β ℂ}
    (hΦ : IsKrausCPTP Φ) (hσ : σ.PosDef) (hτ : τ.PosDef)
    (hmap : Φ σ = τ) :
    IsHilbertSchmidtContraction (weightedHilbertSchmidtMap Φ σ τ) := by
  intro X
  rw [trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq]
  have hNorm := weightedHilbertSchmidtMap_norm_le hΦ hσ hτ hmap X
  nlinarith [norm_nonneg (weightedHilbertSchmidtMap Φ σ τ X), norm_nonneg X]

end Matrix
