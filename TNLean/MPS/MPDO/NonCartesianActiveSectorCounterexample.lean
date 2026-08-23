/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.NonCartesianActiveSectorObstruction
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.Wielandt.Primitivity.Equivalence

/-!
# Normalization of the non-Cartesian counterexample

The candidate is expressed as a nonzero scalar multiple of a normal tensor.
Together with its analytic properties, this refutes a proposed low-level
implication associated with arXiv:1606.00608, Appendix C.2, Proposition
`prop2to3`, lines 1740--1782. It does not supply the ambient simple-biCF
reconstruction or the line-246 normalization convention of the source.
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Operator

noncomputable section

namespace MPOTensor.NonCartesianActiveSectorCandidate

/-! ### Normal representative before scalar absorption -/

/-- The associated MPS tensor has a nonzero letter. -/
lemma exists_toMPSTensor_apply_ne_zero :
    ∃ i, tensor.toMPSTensor i ≠ 0 := by
  refine ⟨finProdFinEquiv ((0 : Fin 4), (0 : Fin 4)), ?_⟩
  intro hzero
  have hentry := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
  norm_num [MPOTensor.toMPSTensor, tensor, sectorMatrix, leftPairing,
    rightPairing, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat] at hentry

/-- The candidate is a nonzero scalar multiple of a CPSV normal tensor.

The scalar is the positive square root of the Perron value of the unnormalized
transfer map.  Algebraic one-site injectivity supplies primitivity; after the
scalar normalization, a Perron gauge gives a left-canonical representative,
and normal-tensor status is transported back through that gauge.

Source: arXiv:1606.00608, lines 224--235. -/
theorem exists_normalTensor_scalar_representation :
    ∃ (A : MPOTensor 4 2) (mu : ℂ),
      mu ≠ 0 ∧ tensor = mu • A ∧ A.toMPSTensor.IsNormalTensor := by
  let _ : NeZero 2 := ⟨by omega⟩
  have hNormal : Kraus.IsNormal tensor.toMPSTensor :=
    Kraus.IsInjective.isNormal tensor_isInjective
  have hPrimitivePaper : tensor.toMPSTensor.IsPrimitivePaper :=
    MPSTensor.isPrimitivePaper_of_isNormal tensor.toMPSTensor hNormal
  have hIrr : Kraus.IsIrreducibleFamily tensor.toMPSTensor :=
    MPSTensor.isIrreducibleTensor_of_isPrimitivePaper tensor.toMPSTensor hPrimitivePaper
  obtain ⟨rho, r, hrho, hr, hEig⟩ :=
    MPSTensor.exists_posDef_transferMap_eigenvector_of_irreducible tensor.toMPSTensor
      hIrr exists_toMPSTensor_apply_ne_zero
  let mu : ℂ := ((Real.sqrt r : ℝ) : ℂ)
  have hmu : mu ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  let A : MPOTensor 4 2 := mu⁻¹ • tensor
  have hrecover : tensor = mu • A := by
    ext i j beta alpha
    change tensor i j beta alpha = mu * (mu⁻¹ * tensor i j beta alpha)
    rw [← mul_assoc, mul_inv_cancel₀ hmu, one_mul]
  have hAinj : A.IsInjective := by
    exact tensor_isInjective.smul (inv_ne_zero hmu)
  have hANormal : Kraus.IsNormal A.toMPSTensor :=
    Kraus.IsInjective.isNormal hAinj
  have hAPrimitivePaper : A.toMPSTensor.IsPrimitivePaper :=
    MPSTensor.isPrimitivePaper_of_isNormal A.toMPSTensor hANormal
  have hAIrr : Kraus.IsIrreducibleFamily A.toMPSTensor :=
    MPSTensor.isIrreducibleTensor_of_isPrimitivePaper A.toMPSTensor hAPrimitivePaper
  have hmumu : mu⁻¹ * starRingEnd ℂ mu⁻¹ = (r : ℂ)⁻¹ := by
    change (((Real.sqrt r : ℝ) : ℂ))⁻¹ *
        starRingEnd ℂ (((Real.sqrt r : ℝ) : ℂ))⁻¹ = (r : ℂ)⁻¹
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hr.le]
  have hmap :
      Kraus.transferMap A.toMPSTensor =
        (r : ℂ)⁻¹ • Kraus.transferMap tensor.toMPSTensor := by
    apply LinearMap.ext
    intro X
    change Kraus.transferMap (fun i ↦ mu⁻¹ • tensor.toMPSTensor i) X =
      (r : ℂ)⁻¹ • Kraus.transferMap tensor.toMPSTensor X
    rw [MPSTensor.transferMap_smul, hmumu]
  have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hfix : Kraus.transferMap A.toMPSTensor rho = rho := by
    rw [hmap, LinearMap.smul_apply, hEig, smul_smul,
      inv_mul_cancel₀ hr_ne, one_smul]
  have hRadius :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin 2) (Fin 2) ℂ))
            (Kraus.transferMap A.toMPSTensor)) = 1 := by
    simpa using
      (spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp
        (Kraus.transferMap A.toMPSTensor)
        (Kraus.transferMap_isCPMap A.toMPSTensor)
        (MPSTensor.isIrreducibleCP_transferMap_of_isIrreducibleTensor
          A.toMPSTensor hAIrr)
        rho 1 hrho (by norm_num) (by simpa using hfix))
  obtain ⟨sigma, hsigma, hsigmaFix, hLeft, hGauge, hGaugeIrr⟩ :=
    MPSTensor.exists_tpGauge_of_irreducible_spectralRadius_one hAIrr hRadius
  have hGaugeNormal :
      Kraus.IsNormal (MPSTensor.tpGauge A.toMPSTensor sigma) :=
    MPSTensor.isNormal_of_gaugeEquiv hANormal hGauge
  have hGaugeNormalTensor :
      MPSTensor.IsNormalTensor (MPSTensor.tpGauge A.toMPSTensor sigma) :=
    MPSTensor.isNormalTensor_of_isNormal_leftCanonical _ hGaugeNormal hLeft
  have hANormalTensor : A.toMPSTensor.IsNormalTensor :=
    hGaugeNormalTensor.of_gaugeEquiv hGauge
  exact ⟨A, mu, hmu, hrecover, hANormalTensor⟩

/-- Counterexample to the low-level implication asserting that injectivity,
SAL, literal physical-trace idempotence, and being a nonzero scalar multiple
of a normal tensor yield a neighboring trace factorization.

This theorem does not package the ambient simple-biCF canonical reconstruction
or the global unit-weight convention assumed in arXiv:1606.00608, lines
217--246 and 1626--1665. It therefore does not refute the source-context
implication `(ii) ⇒ (iv)`. See `docs/paper-gaps/cpgsv17_pf_rank_one.tex` and
`docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`. -/
theorem full_lowLevel_counterexample :
    ∃ (K A : MPOTensor 4 2) (mu : ℂ),
      mu ≠ 0 ∧ K = mu • A ∧ A.toMPSTensor.IsNormalTensor ∧
      K.IsInjective ∧ K.IsSAL ∧
      physTraceTransfer K * physTraceTransfer K = physTraceTransfer K ∧
      (¬∃ F : PhysicalSectorFactorization K,
        Nonempty F.NeighboringTraceFactorization) := by
  obtain ⟨A, mu, hmu, hrecover, hNormal⟩ :=
    exists_normalTensor_scalar_representation
  exact ⟨tensor, A, mu, hmu, hrecover, hNormal, tensor_isInjective,
    tensor_isSAL, physTraceTransfer_tensor_idempotent,
    not_exists_neighboringTraceFactorization⟩

end MPOTensor.NonCartesianActiveSectorCandidate
