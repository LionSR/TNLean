/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausGauge
import TNLean.MPS.MPDO.NonCartesianActiveSectorObstruction
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.Wielandt.Primitivity.Equivalence

/-!
# Normalization of the rank-one neighboring-trace obstruction

The four-letter tensor has no physical-sector factorization whose neighboring
traces satisfy `tr(η_{k,h}) = a_k b_h` and `∑_k a_k b_k = 1`. This module
expresses that obstruction tensor as a nonzero scalar multiple of a normal
tensor. Together with its analytic properties, this refutes a proposed
low-level implication associated with arXiv:1606.00608, Appendix C.2,
Proposition `prop2to3`, lines 1740--1782. It does not supply the ambient
simple-biCF reconstruction or the line-246 normalization convention of the
source.

This is project-derived auxiliary counterexample infrastructure, not a result
asserted by arXiv:1606.00608. The paper's lines 217--246, 1628--1665, and
1740--1782 provide only the normal-block, simple-biCF, and per-block reduction
context.

The filename and namespace retain the older project term "non-Cartesian";
CPSV16 does not use that term for the neighboring-trace factorization.
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Operator

noncomputable section

namespace MPOTensor.NonCartesianActiveSectorCandidate

/-! ### Normal representative before scalar absorption -/

/-! #### An exact upper bound for the normalizing coefficient -/

/-- A positive test matrix used to bound the Perron eigenvalue of the
candidate's associated completely positive map.

This is a counterexample-specific helper for the coefficient normalization
`|μ_k| ≤ 1` in arXiv:1606.00608, line 246, not a theorem asserted in the
source. -/
private def normalizingCoefficientWitness : Matrix (Fin 2) (Fin 2) ℂ :=
  !![20, 0; 0, 1]

/-- The exact value of the candidate's adjoint transfer map on the test
matrix. -/
private lemma adjointMap_normalizingCoefficientWitness :
    Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness =
      !![75 / 8, 9 / 40; 9 / 40, 303 / 5000] := by
  have hletter (p q : Fin 4) :
      tensor.toMPSTensor (finProdFinEquiv (p, q)) =
        if p = q then sectorMatrix p else 0 := by
    change tensor (finProdFinEquiv (p, q)).divNat
        (finProdFinEquiv (p, q)).modNat = _
    rw [MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]
    rfl
  have hadj :
      Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness =
        ∑ k : Fin 4,
          (sectorMatrix k)ᴴ * normalizingCoefficientWitness * sectorMatrix k := by
    rw [Kraus.adjointMap_apply]
    rw [← Equiv.sum_comp (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin (4 * 4))]
    rw [Fintype.sum_prod_type]
    simp_rw [hletter]
    simp [Fin.sum_univ_four]
  rw [hadj]
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j
  all_goals
    simp only [normalizingCoefficientWitness, sectorMatrix, leftPairing,
      rightPairing, Fin.sum_univ_four, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.of_apply,
      Matrix.vecMulVec]
    norm_num [Matrix.star_apply]

/-- The upper-triangular factor in the exact congruence certificate for the
positive-definite adjoint-transfer gap. -/
private def normalizingCoefficientGapFactor : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, -9 / 425; 0, 1]

/-- The positive diagonal factor in the exact congruence certificate for the
adjoint-transfer gap. -/
private def normalizingCoefficientGapDiagonal :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![85 / 8, 19861 / 21250]

/-- The exact positive-definite gap between the test matrix and its adjoint
transfer image.

Its `Uᴴ D U` factorization has diagonal entries `85 / 8` and
`19861 / 21250`, hence determinant `19861 / 2000`. -/
private lemma normalizingCoefficientWitness_sub_adjointMap_posDef :
    (normalizingCoefficientWitness -
      Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness).PosDef := by
  have hFactorization :
      normalizingCoefficientWitness -
          Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness =
        normalizingCoefficientGapFactorᴴ * normalizingCoefficientGapDiagonal *
          normalizingCoefficientGapFactor := by
    rw [adjointMap_normalizingCoefficientWitness]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp only [normalizingCoefficientWitness, normalizingCoefficientGapFactor,
        normalizingCoefficientGapDiagonal, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.conjTranspose_apply]
      norm_num
  rw [hFactorization]
  have hDiagonal : normalizingCoefficientGapDiagonal.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [normalizingCoefficientGapDiagonal]
  apply hDiagonal.conjTranspose_mul_mul_same
  intro x y hxy
  have h1 : x 1 = y 1 := by
    have := congrFun hxy (1 : Fin 2)
    simpa [normalizingCoefficientGapFactor, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using this
  funext i
  fin_cases i
  · have h0 := congrFun hxy (0 : Fin 2)
    simp only [Matrix.mulVec, dotProduct, normalizingCoefficientGapFactor,
      Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.sum_univ_two,
      one_mul, Matrix.cons_val_one] at h0
    rw [h1] at h0
    simpa using h0
  · exact h1

/-- The positive test matrix is positive definite. -/
private lemma normalizingCoefficientWitness_posDef :
    normalizingCoefficientWitness.PosDef := by
  rw [show normalizingCoefficientWitness = Matrix.diagonal ![(20 : ℂ), 1] by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [normalizingCoefficientWitness]]
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num

/-- A positive-definite eigenmatrix of the candidate's associated completely
positive map has eigenvalue strictly smaller than one.

This is the one-sector estimate needed for the coefficient bound in
arXiv:1606.00608, line 246. It is a counterexample helper, not the source
theorem: the source additionally normalizes an ambient simple biCF tensor so
that one of all its sector coefficients has modulus one. -/
lemma transferMap_posDef_eigenvalue_lt_one
    {rho : Matrix (Fin 2) (Fin 2) ℂ} {r : ℝ}
    (hrho : rho.PosDef)
    (hEig : Kraus.transferMap tensor.toMPSTensor rho = (r : ℂ) • rho) :
    r < 1 := by
  have htraceNonneg :
      0 ≤ Matrix.trace (normalizingCoefficientWitness * rho) :=
    Matrix.PosSemidef.trace_mul_nonneg
      normalizingCoefficientWitness_posDef.posSemidef hrho.posSemidef
  have htraceNe :
      Matrix.trace (normalizingCoefficientWitness * rho) ≠ 0 := by
    intro hzero
    exact (Matrix.PosDef.isUnit hrho).ne_zero
      (Kraus.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero
        hrho.posSemidef normalizingCoefficientWitness_posDef hzero)
  have htracePos :
      0 < Matrix.trace (normalizingCoefficientWitness * rho) :=
    lt_of_le_of_ne htraceNonneg
      (by simpa only [ne_eq, eq_comm] using htraceNe)
  have hgapNonneg :
      0 ≤ Matrix.trace
        ((normalizingCoefficientWitness -
          Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness) *
            rho) :=
    Matrix.PosSemidef.trace_mul_nonneg
      normalizingCoefficientWitness_sub_adjointMap_posDef.posSemidef
      hrho.posSemidef
  have hgapNe :
      Matrix.trace
        ((normalizingCoefficientWitness -
          Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness) *
            rho) ≠ 0 := by
    intro hzero
    exact (Matrix.PosDef.isUnit hrho).ne_zero
      (Kraus.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero
        hrho.posSemidef normalizingCoefficientWitness_sub_adjointMap_posDef hzero)
  have hgapPos :
      0 < Matrix.trace
        ((normalizingCoefficientWitness -
          Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness) *
            rho) :=
    lt_of_le_of_ne hgapNonneg (by simpa only [ne_eq, eq_comm] using hgapNe)
  have hEigMap :
      Kraus.map tensor.toMPSTensor rho = (r : ℂ) • rho := by
    rw [← Kraus.mapLM_apply]
    exact hEig
  have hgapTrace :
      Matrix.trace
          ((normalizingCoefficientWitness -
            Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness) *
              rho) =
        (((1 - r : ℝ) : ℂ) *
          Matrix.trace (normalizingCoefficientWitness * rho)) := by
    calc
      Matrix.trace
          ((normalizingCoefficientWitness -
            Kraus.adjointMap tensor.toMPSTensor normalizingCoefficientWitness) *
              rho) =
          Matrix.trace (normalizingCoefficientWitness * rho) -
            Matrix.trace
              (Kraus.adjointMap tensor.toMPSTensor
                normalizingCoefficientWitness * rho) := by
              rw [Matrix.sub_mul, Matrix.trace_sub]
      _ = Matrix.trace (normalizingCoefficientWitness * rho) -
            Matrix.trace
              (normalizingCoefficientWitness *
                Kraus.map tensor.toMPSTensor rho) := by
              rw [Kraus.trace_mul_map_eq_trace_adjointMap_mul]
      _ = Matrix.trace (normalizingCoefficientWitness * rho) -
            Matrix.trace
              (normalizingCoefficientWitness * ((r : ℂ) • rho)) := by
              rw [hEigMap]
      _ = (((1 - r : ℝ) : ℂ) *
            Matrix.trace (normalizingCoefficientWitness * rho)) := by
              rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
              push_cast
              ring
  rw [hgapTrace] at hgapPos
  have hrealPos :
      0 < (1 - r) *
        (Matrix.trace (normalizingCoefficientWitness * rho)).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using (Complex.pos_iff.mp hgapPos).1
  have htraceRealPos :
      0 < (Matrix.trace (normalizingCoefficientWitness * rho)).re :=
    (Complex.pos_iff.mp htracePos).1
  nlinarith

/-- A positive-definite eigenmatrix of the candidate's associated completely
positive map has eigenvalue at most one.

This records the non-strict coefficient bound in arXiv:1606.00608, line 246,
as an immediate consequence of the candidate's strict estimate. -/
lemma transferMap_posDef_eigenvalue_le_one
    {rho : Matrix (Fin 2) (Fin 2) ℂ} {r : ℝ}
    (hrho : rho.PosDef)
    (hEig : Kraus.transferMap tensor.toMPSTensor rho = (r : ℂ) • rho) :
    r ≤ 1 :=
  (transferMap_posDef_eigenvalue_lt_one hrho hEig).le

/-- The associated MPS tensor has a nonzero letter. -/
lemma exists_toMPSTensor_apply_ne_zero :
    ∃ i, tensor.toMPSTensor i ≠ 0 := by
  refine ⟨finProdFinEquiv ((0 : Fin 4), (0 : Fin 4)), ?_⟩
  intro hzero
  have hentry := congrFun (congrFun hzero (0 : Fin 2)) (0 : Fin 2)
  norm_num [MPOTensor.toMPSTensor, tensor, sectorMatrix, leftPairing,
    rightPairing, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat] at hentry

/-- The candidate is a nonzero scalar multiple of a normal tensor whose
Perron-gauged representative is injective and left-canonical.

The scalar is the positive square root of the Perron value of the unnormalized
completely positive map. Algebraic one-site injectivity supplies primitivity;
after scalar normalization, the already-constructed Perron gauge gives the
representative `B`. The exact test-matrix estimate above gives
`0 < |μ| < 1`. -/
private theorem exists_scalar_and_leftCanonical_normalTensor_representations :
    ∃ (A : MPOTensor 4 2) (mu : ℂ) (B : MPSTensor (4 * 4) 2),
      mu ≠ 0 ∧ ‖mu‖ < 1 ∧ tensor = mu • A ∧
        MPSTensor.GaugeEquiv A.toMPSTensor B ∧
        Kraus.IsInjective B ∧ MPSTensor.IsLeftCanonical B ∧
        MPSTensor.IsNormalTensor B ∧
        MPSTensor.GaugeEquiv tensor.toMPSTensor (mu • B) := by
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
  have hr_lt_one : r < 1 :=
    transferMap_posDef_eigenvalue_lt_one hrho hEig
  let mu : ℂ := ((Real.sqrt r : ℝ) : ℂ)
  have hmu : mu ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  have hmu_norm : ‖mu‖ < 1 := by
    change ‖((Real.sqrt r : ℝ) : ℂ)‖ < 1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg r)]
    exact (Real.sqrt_lt hr.le (by norm_num)).2 (by simpa using hr_lt_one)
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
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily
          A.toMPSTensor hAIrr)
        rho 1 hrho (by norm_num) (by simpa using hfix))
  obtain ⟨sigma, hsigma, hsigmaFix, hLeft, hGauge, hGaugeIrr⟩ :=
    MPSTensor.exists_tpGauge_of_irreducible_spectralRadius_one hAIrr hRadius
  have hGaugeNormal :
      Kraus.IsNormal (Kraus.tpGauge A.toMPSTensor sigma) :=
    MPSTensor.isNormal_of_gaugeEquiv hANormal hGauge
  have hGaugeNormalTensor :
      MPSTensor.IsNormalTensor (Kraus.tpGauge A.toMPSTensor sigma) :=
    MPSTensor.isNormalTensor_of_isNormal_leftCanonical _ hGaugeNormal hLeft
  have hGaugeInjective :
      Kraus.IsInjective (Kraus.tpGauge A.toMPSTensor sigma) :=
    MPSTensor.isInjective_of_gaugeEquiv hAinj hGauge
  have hTensorGauge :
      MPSTensor.GaugeEquiv tensor.toMPSTensor
        (mu • Kraus.tpGauge A.toMPSTensor sigma) := by
    obtain ⟨X, hX⟩ := hGauge
    refine ⟨X, fun i ↦ ?_⟩
    have hrecoverMPS := congrFun (congrArg MPOTensor.toMPSTensor hrecover) i
    change mu • Kraus.tpGauge A.toMPSTensor sigma i =
      X * tensor.toMPSTensor i * X⁻¹
    rw [hX i, hrecoverMPS]
    change mu • (X * A.toMPSTensor i * X⁻¹) =
      X * (mu • A.toMPSTensor i) * X⁻¹
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  exact ⟨A, mu, Kraus.tpGauge A.toMPSTensor sigma, hmu, hmu_norm,
    hrecover, hGauge, hGaugeInjective, hLeft, hGaugeNormalTensor, hTensorGauge⟩

/-- The candidate has an injective, left-canonical normal representative with
a nonzero coefficient of norm strictly below one and the required gauge
relation after scalar absorption. -/
theorem exists_leftCanonical_normalTensor_scalar_representation :
    ∃ (mu : ℂ) (B : MPSTensor (4 * 4) 2),
      mu ≠ 0 ∧ ‖mu‖ < 1 ∧ Kraus.IsInjective B ∧
        MPSTensor.IsLeftCanonical B ∧ MPSTensor.IsNormalTensor B ∧
        MPSTensor.GaugeEquiv tensor.toMPSTensor (mu • B) := by
  obtain ⟨_, mu, B, hmu, hmuNorm, _, _, hBInj, hBLeft, hBNormal,
      hTensorGauge⟩ :=
    exists_scalar_and_leftCanonical_normalTensor_representations
  exact ⟨mu, B, hmu, hmuNorm, hBInj, hBLeft, hBNormal, hTensorGauge⟩

/-- The candidate is a nonzero scalar multiple of a normal tensor.

This is the original companion statement obtained from the same normalized
representative construction. -/
theorem exists_normalTensor_scalar_representation :
    ∃ (A : MPOTensor 4 2) (mu : ℂ),
      mu ≠ 0 ∧ ‖mu‖ < 1 ∧ tensor = mu • A ∧
        A.toMPSTensor.IsNormalTensor := by
  obtain ⟨A, mu, _, hmu, hmuNorm, hrecover, hGauge, _, _, hBNormal, _⟩ :=
    exists_scalar_and_leftCanonical_normalTensor_representations
  exact ⟨A, mu, hmu, hmuNorm, hrecover, hBNormal.of_gaugeEquiv hGauge⟩

/-- Counterexample to the low-level implication asserting that injectivity,
SAL, literal physical-trace idempotence, and being a nonzero scalar multiple
of a normal tensor with coefficient norm strictly between zero and one yield a
neighboring trace factorization.

This theorem does not package the ambient simple-biCF canonical reconstruction
or the global unit-weight convention assumed in arXiv:1606.00608, lines
217--246 and 1626--1665. It therefore does not refute the source-context
implication `(ii) ⇒ (iv)`. See
<https://sirui-lu.com/QICLean/paper-gaps/cpgsv17_pf_rank_one.pdf> and
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>. -/
theorem full_lowLevel_counterexample :
    ∃ (K A : MPOTensor 4 2) (mu : ℂ),
      mu ≠ 0 ∧ ‖mu‖ < 1 ∧ K = mu • A ∧ A.toMPSTensor.IsNormalTensor ∧
      K.IsInjective ∧ K.IsSAL ∧
      physTraceTransfer K * physTraceTransfer K = physTraceTransfer K ∧
      (¬∃ F : PhysicalSectorFactorization K,
        Nonempty F.NeighboringTraceFactorization) := by
  obtain ⟨A, mu, hmu, hmu_norm, hrecover, hNormal⟩ :=
    exists_normalTensor_scalar_representation
  exact ⟨tensor, A, mu, hmu, hmu_norm, hrecover, hNormal, tensor_isInjective,
    tensor_isSAL, physTraceTransfer_tensor_idempotent,
    not_exists_neighboringTraceFactorization⟩

end MPOTensor.NonCartesianActiveSectorCandidate
