/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FrobeniusHilbert
import TNLean.Algebra.MatrixFamilySupport
import TNLean.Algebra.MatrixCongruence
import TNLean.Algebra.RectangularChoi
import TNLean.Analysis.CoisometricCompression
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.Peripheral.UnitalKraus
import TNLean.Channel.SingleKraus
import TNLean.Channel.Spectral.Support

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
* `Matrix.supportedWeightedHilbertSchmidtMap`: the weighted channel map with
  the negative output power restricted to its support.
* `Matrix.supportedWeightedHilbertSchmidtMap_norm_le`: the contraction bound
  without a full-support assumption on the output.

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

/-! ### Singular output support -/

/-- If a channel sends a positive-definite matrix to `τ`, then every output of the
channel is supported on the support projection of `τ`.

This is the support statement underlying the singular-output specialization of
Beigi, arXiv:1306.5920, Theorem 6 and equation (18). -/
theorem IsKrausCPTP.supportProj_mul_map
    {r p : ℕ} {Φ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ}
    {σ : Matrix (Fin r) (Fin r) ℂ} {τ : Matrix (Fin p) (Fin p) ℂ}
    (hΦ : IsKrausCPTP Φ) (hσ : σ.PosDef) (hmap : Φ σ = τ)
    (X : Matrix (Fin r) (Fin r) ℂ) :
    (hΦ.map_posSemidef hσ.posSemidef).supportProj * Φ X = Φ X := by
  obtain ⟨d, A, hA⟩ := hΦ.isKrausCP
  let sσ := CFC.sqrt σ
  let B : Fin d → Matrix (Fin p) (Fin r) ℂ := fun i ↦ A i * sσ
  have hsσ_psd : sσ.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)
  have hsσ_sq : sσ * sσ = σ := by
    simpa only [sσ] using CFC.sqrt_mul_sqrt_self σ hσ.posSemidef.nonneg
  have hsσ_star : sσᴴ = sσ := hsσ_psd.isHermitian.eq
  have hsσ_unit : IsUnit sσ :=
    (CFC.isUnit_sqrt_iff σ hσ.posSemidef.nonneg).2 hσ.isUnit
  have hsσ_det : sσ.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det sσ).1 hsσ_unit).ne_zero
  have hGram : familyColumnGram B = τ := by
    rw [familyColumnGram_eq_sum]
    calc
      ∑ i, B i * (B i)ᴴ = ∑ i, A i * σ * (A i)ᴴ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [B, Matrix.conjTranspose_mul, hsσ_star]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc sσ sσ, hsσ_sq]
      _ = Φ σ := (hA σ).symm
      _ = τ := hmap
  have hSupport :
      (hΦ.map_posSemidef hσ.posSemidef).supportProj = familySupportProj B := by
    exact ((familyColumnGram_posSemidef B).supportProj_congr
      (hΦ.map_posSemidef hσ.posSemidef) (hGram.trans hmap.symm)).symm
  rw [hSupport, hA, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hPA : familySupportProj B * A i = A i := by
    calc
      familySupportProj B * A i =
          (familySupportProj B * A i) * (1 : Matrix (Fin r) (Fin r) ℂ) := by
        rw [Matrix.mul_one]
      _ = (familySupportProj B * A i) * (sσ * sσ⁻¹) := by
        rw [Matrix.mul_nonsing_inv sσ (Ne.isUnit hsσ_det)]
      _ = (familySupportProj B * (A i * sσ)) * sσ⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = (familySupportProj B * B i) * sσ⁻¹ := rfl
      _ = B i * sσ⁻¹ := by rw [familySupportProj_mul]
      _ = (A i * sσ) * sσ⁻¹ := rfl
      _ = A i * (sσ * sσ⁻¹) := Matrix.mul_assoc _ _ _
      _ = A i := by rw [Matrix.mul_nonsing_inv sσ (Ne.isUnit hsσ_det), Matrix.mul_one]
  simp only [← Matrix.mul_assoc, hPA]

/-- Under the hypotheses of `IsKrausCPTP.supportProj_mul_map`, every channel
output is also supported on the right. -/
theorem IsKrausCPTP.map_mul_supportProj
    {r p : ℕ} {Φ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ}
    {σ : Matrix (Fin r) (Fin r) ℂ} {τ : Matrix (Fin p) (Fin p) ℂ}
    (hΦ : IsKrausCPTP Φ) (hσ : σ.PosDef) (hmap : Φ σ = τ)
    (X : Matrix (Fin r) (Fin r) ℂ) :
    Φ X * (hΦ.map_posSemidef hσ.posSemidef).supportProj = Φ X := by
  have hleft := Matrix.IsKrausCPTP.supportProj_mul_map hΦ hσ hmap Xᴴ
  have hΦpos : IsPositiveMap Φ := fun Y hY ↦ hΦ.map_posSemidef hY
  have hstar := congrArg Matrix.conjTranspose hleft
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (hΦ.map_posSemidef hσ.posSemidef).supportProj_isHermitian.eq,
    hΦpos.map_conjTranspose] using hstar

/-- Compress the output of a matrix map along an isometry `V`. -/
noncomputable def outputSupportCompressedMap
    {r p s : ℕ} (Φ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (V : Matrix (Fin p) (Fin s) ℂ) :
    Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin s) (Fin s) ℂ :=
  (singleKrausMap Vᴴ).comp Φ

/-- Compression of a channel to the support of the image of a faithful weight
is again trace preserving and completely positive. -/
theorem outputSupportCompressedMap_isKrausCPTP
    {r p s : ℕ} {Φ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ}
    {σ : Matrix (Fin r) (Fin r) ℂ} {τ : Matrix (Fin p) (Fin p) ℂ}
    (hΦ : IsKrausCPTP Φ) (hσ : σ.PosDef) (hmap : Φ σ = τ)
    (V : Matrix (Fin p) (Fin s) ℂ)
    (hVVt : V * Vᴴ = (hΦ.map_posSemidef hσ.posSemidef).supportProj) :
    IsKrausCPTP (outputSupportCompressedMap Φ V) := by
  apply isKrausCPTP_of_isKrausCP_trace_preserving
  · exact isKrausCP_comp hΦ.isKrausCP (singleKrausMap_isKrausCP Vᴴ)
  · intro X
    rw [outputSupportCompressedMap, LinearMap.comp_apply, singleKrausMap_apply,
      Matrix.conjTranspose_conjTranspose]
    calc
      Matrix.trace (Vᴴ * Φ X * V) = Matrix.trace (V * Vᴴ * Φ X) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace
          ((hΦ.map_posSemidef hσ.posSemidef).supportProj * Φ X) := by rw [hVVt]
      _ = Matrix.trace (Φ X) := by rw [Matrix.IsKrausCPTP.supportProj_mul_map hΦ hσ hmap]
      _ = Matrix.trace X := hΦ.trace_map X

/-- The support-weighted map
`X ↦ τ⁻¹⁄⁴ Φ(σ¹⁄⁴ X σ¹⁄⁴) τ⁻¹⁄⁴`, with the negative power
zero on the kernel of `τ`. -/
noncomputable def supportedWeightedHilbertSchmidtMap
    {r p : ℕ} (Φ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ)
    (σ : Matrix (Fin r) (Fin r) ℂ) {τ : Matrix (Fin p) (Fin p) ℂ}
    (hτ : τ.PosSemidef) :
    Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ :=
  (singleKrausMap hτ.supportInvFourthRoot).comp
    (Φ.comp (singleKrausMap (CFC.sqrt (CFC.sqrt σ))))

/-- Expansion along an isometry preserves the Frobenius norm. -/
theorem frobenius_norm_isometry_mul_mul_conjTranspose
    {p s : ℕ} (V : Matrix (Fin p) (Fin s) ℂ) (hV : Vᴴ * V = 1)
    (Z : Matrix (Fin s) (Fin s) ℂ) :
    ‖V * Z * Vᴴ‖ = ‖Z‖ := by
  have hsquare : ‖V * Z * Vᴴ‖ ^ 2 = ‖Z‖ ^ 2 := by
    rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
      ← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V (Z * Vᴴ), hV, Matrix.one_mul]
    rw [Matrix.trace_mul_comm V (Zᴴ * (Z * Vᴴ))]
    rw [Matrix.mul_assoc Zᴴ (Z * Vᴴ) V, Matrix.mul_assoc Z Vᴴ V,
      hV, Matrix.mul_one]
  nlinarith [norm_nonneg (V * Z * Vᴴ), norm_nonneg Z]

/-- Compression proof of the support-weighted contraction with a named output
weight and an explicit proof of its positivity. -/
private theorem supportedWeightedHilbertSchmidtMap_norm_le_aux
    {r p : ℕ} {Φ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ}
    {σ : Matrix (Fin r) (Fin r) ℂ} {τ : Matrix (Fin p) (Fin p) ℂ}
    (hΦ : IsKrausCPTP Φ) (hσ : σ.PosDef) (hτ : τ.PosSemidef)
    (hmap : Φ σ = τ) (X : Matrix (Fin r) (Fin r) ℂ) :
    ‖supportedWeightedHilbertSchmidtMap Φ σ hτ X‖ ≤ ‖X‖ := by
  obtain ⟨s, V, hV, hVrange⟩ :=
    hτ.isOrthogonalProjection_supportProj.exists_range_isometry
  have hSupport :
      (hΦ.map_posSemidef hσ.posSemidef).supportProj = hτ.supportProj := by
    exact (hΦ.map_posSemidef hσ.posSemidef).supportProj_congr hτ hmap
  let Ψ := outputSupportCompressedMap Φ V
  let τc := Vᴴ * τ * V
  have hΨ : IsKrausCPTP Ψ := by
    apply outputSupportCompressedMap_isKrausCPTP hΦ hσ hmap V
    exact hVrange.trans hSupport.symm
  have hτc : τc.PosDef := by
    have h := hτ.compression_on_support_posDef (V := Vᴴ)
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hV)
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hVrange)
    simpa only [τc, Matrix.conjTranspose_conjTranspose] using h
  have hmapc : Ψ σ = τc := by
    simp only [Ψ, τc, outputSupportCompressedMap, LinearMap.comp_apply,
      singleKrausMap_apply, Matrix.conjTranspose_conjTranspose, hmap]
  let q := hτ.supportInvFourthRoot
  let qc := (CFC.sqrt (CFC.sqrt τc))⁻¹
  have hqcomp : Vᴴ * q * V = qc := by
    simpa only [q, qc, τc] using
      hτ.supportInvFourthRoot_compression_on_support V hV hVrange
  have hPq : hτ.supportProj * q = q := by
    let hsτ : (CFC.sqrt τ).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg τ)
    change hτ.supportProj * hsτ.supportInvSqrt = hsτ.supportInvSqrt
    rw [← hτ.supportProj_cfc_sqrt]
    exact hsτ.supportProj_mul_supportInvSqrt
  have hqP : q * hτ.supportProj = q := by
    let hsτ : (CFC.sqrt τ).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg τ)
    change hsτ.supportInvSqrt * hτ.supportProj = hsτ.supportInvSqrt
    rw [← hτ.supportProj_cfc_sqrt]
    exact hsτ.supportInvSqrt_mul_supportProj
  have hqstar : qᴴ = q := by
    exact (Matrix.nonneg_iff_posSemidef.mp
      (CFC.sqrt_nonneg τ)).supportInvSqrt_isHermitian.eq
  let qσ := CFC.sqrt (CFC.sqrt σ)
  let Y := Φ (qσ * X * qσ)
  have hPY : hτ.supportProj * Y = Y := by
    rw [← hSupport]
    exact Matrix.IsKrausCPTP.supportProj_mul_map hΦ hσ hmap (qσ * X * qσ)
  have hYP : Y * hτ.supportProj = Y := by
    rw [← hSupport]
    exact Matrix.IsKrausCPTP.map_mul_supportProj hΦ hσ hmap (qσ * X * qσ)
  let Z := weightedHilbertSchmidtMap Ψ σ τc X
  have hZnorm : ‖Z‖ ≤ ‖X‖ :=
    weightedHilbertSchmidtMap_norm_le hΨ hσ hτc hmapc X
  have hqσstar : qσᴴ = qσ := by
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (CFC.sqrt σ))).isHermitian.eq
  have hqcstar : qcᴴ = qc := by
    dsimp only [qc]
    rw [Matrix.conjTranspose_nonsing_inv]
    exact congrArg Inv.inv
      (Matrix.nonneg_iff_posSemidef.mp
        (CFC.sqrt_nonneg (CFC.sqrt τc))).isHermitian.eq
  have hZ : Z = qc * (Vᴴ * Y * V) * qc := by
    simp only [Z, weightedHilbertSchmidtMap, LinearMap.comp_apply,
      singleKrausMap_apply, Ψ, outputSupportCompressedMap,
      Matrix.conjTranspose_conjTranspose, hqσstar, qσ, Y, qc, hqcstar]
  have hembed : V * Z * Vᴴ = q * Y * q := by
    rw [hZ, ← hqcomp]
    calc
      V * ((Vᴴ * q * V) * (Vᴴ * Y * V) * (Vᴴ * q * V)) * Vᴴ =
          (V * Vᴴ) * q * (V * Vᴴ) * Y * (V * Vᴴ) * q * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = hτ.supportProj * q * hτ.supportProj * Y *
          hτ.supportProj * q * hτ.supportProj := by rw [hVrange]
      _ = q * Y * q := by
        simp only [Matrix.mul_assoc, hPq, hqP, hYP]
  have hsupported : supportedWeightedHilbertSchmidtMap Φ σ hτ X = q * Y * q := by
    simp only [supportedWeightedHilbertSchmidtMap, LinearMap.comp_apply,
      singleKrausMap_apply, hqstar, hqσstar, q, qσ, Y]
  rw [hsupported, ← hembed, frobenius_norm_isometry_mul_mul_conjTranspose V hV]
  exact hZnorm

/-- The support-weighted `p = 2` specialization of the Schatten-norm
contraction in Beigi, arXiv:1306.5920, Theorem 6 and equation (18).

No full-support hypothesis is imposed on the output `Φ σ`; its negative
quarter power vanishes on the kernel. -/
theorem supportedWeightedHilbertSchmidtMap_norm_le
    {r p : ℕ} {Φ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ}
    {σ : Matrix (Fin r) (Fin r) ℂ}
    (hΦ : IsKrausCPTP Φ) (hσ : σ.PosDef) (X : Matrix (Fin r) (Fin r) ℂ) :
    ‖supportedWeightedHilbertSchmidtMap Φ σ
      (hΦ.map_posSemidef hσ.posSemidef) X‖ ≤ ‖X‖ := by
  exact supportedWeightedHilbertSchmidtMap_norm_le_aux hΦ hσ
    (hΦ.map_posSemidef hσ.posSemidef) rfl X

/-- The support-weighted channel map is a Hilbert--Schmidt contraction without
a full-support assumption on the output weight. -/
theorem supportedWeightedHilbertSchmidtMap_isHilbertSchmidtContraction
    {r p : ℕ} {Φ : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ}
    {σ : Matrix (Fin r) (Fin r) ℂ}
    (hΦ : IsKrausCPTP Φ) (hσ : σ.PosDef) :
    IsHilbertSchmidtContraction
      (supportedWeightedHilbertSchmidtMap Φ σ
        (hΦ.map_posSemidef hσ.posSemidef)) := by
  intro X
  rw [trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq]
  have hNorm := supportedWeightedHilbertSchmidtMap_norm_le hΦ hσ X
  nlinarith [norm_nonneg
    (supportedWeightedHilbertSchmidtMap Φ σ
      (hΦ.map_posSemidef hσ.posSemidef) X), norm_nonneg X]

-- The contraction specializes to the identity channel on the two-dimensional matrix algebra.
private theorem weightedHilbertSchmidtMap_identity_fin_two
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖weightedHilbertSchmidtMap
      (LinearMap.id : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
      1 1 X‖ ≤ ‖X‖ := by
  exact weightedHilbertSchmidtMap_norm_le isKrausCPTP_id
    Matrix.PosDef.one Matrix.PosDef.one rfl X

-- The same specialization remains valid for the zero-dimensional matrix algebra.
private theorem weightedHilbertSchmidtMap_identity_fin_zero
    (X : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖weightedHilbertSchmidtMap
      (LinearMap.id : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ)
      1 1 X‖ ≤ ‖X‖ := by
  exact weightedHilbertSchmidtMap_norm_le isKrausCPTP_id
    Matrix.PosDef.one Matrix.PosDef.one rfl X

-- The support-weighted theorem includes the zero-dimensional output algebra.
private theorem supportedWeightedHilbertSchmidtMap_identity_fin_zero
    (X : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖supportedWeightedHilbertSchmidtMap
      (LinearMap.id : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ)
      1 (isKrausCPTP_id.map_posSemidef Matrix.PosDef.one.posSemidef) X‖ ≤ ‖X‖ := by
  exact supportedWeightedHilbertSchmidtMap_norm_le isKrausCPTP_id Matrix.PosDef.one X

end Matrix
