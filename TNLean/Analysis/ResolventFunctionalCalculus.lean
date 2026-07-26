/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixSqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Functional calculus from common resolvent vectors

This file records the finite-dimensional passage from equality of resolvents on
a fixed vector to equality of the positive square roots on that vector.

## Main results

* `Matrix.sqrt_mulVec_eq_of_resolvent_mulVec_eq` shows that if two positive
  semidefinite matrices have the same shifted inverse on a vector for every
  positive shift, then their positive square roots agree on that vector.
* `Matrix.mulVec_sqrt_mulVec_eq_of_mulVec_resolvent_mulVec_eq` gives the same
  conclusion after applying a fixed matrix to the resolvent and square-root
  vectors.
* `Matrix.sourceB_resolvent_eq_relativeModular` factors the source-`B`
  left--right resolvent through the relative modular Kronecker matrix.
* `Matrix.relativeModular_sqrt_mulVec_vec_one` evaluates its positive square
  root on the vectorized identity.

## References

* A. Jenčová and M. B. Ruskai, *A Unified Treatment of Convexity of Relative
  Entropy and Related Trace Functions, with Conditions for Equality*,
  arXiv:0903.2895v4, lines 658–680.
-/

open Filter MeasureTheory Set
open scoped Matrix ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

private instance {n : Type*} [Fintype n] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint := by
  letI := Classical.decEq n
  exact ContinuousFunctionalCalculus.toNonUnital

/-- Resolvent form of the Löwner real-power integrand. -/
private lemma cfc_rpowIntegrand₀₁_eq_resolvent
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {p t : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) :
    cfc (Real.rpowIntegrand₀₁ p t) A =
      t ^ (p - 1) • (1 : Matrix n n ℂ) -
        t ^ p • (t • (1 : Matrix n n ℂ) + A)⁻¹ := by
  have hA_nonneg : (0 : Matrix n n ℂ) ≤ A :=
    Matrix.nonneg_iff_posSemidef.mpr hA
  rw [Real.rpowIntegrand₀₁_eq_sub (ne_of_lt hp.2) ht]
  have hg : ContinuousOn (fun z : ℝ ↦ (t + z)⁻¹) (spectrum ℝ A) := by
    apply (continuous_const.add continuous_id).continuousOn.inv₀
    intro z hz
    have hz_nonneg := spectrum_nonneg_of_nonneg hA_nonneg hz
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht hz_nonneg)
  have hspectrum : ∀ r ∈ spectrum ℝ A, t + r ≠ 0 := by
    intro r hr
    have hr_nonneg := spectrum_nonneg_of_nonneg hA_nonneg hr
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht hr_nonneg)
  have hself : IsSelfAdjoint A := hA.isHermitian
  have hg_mul : ContinuousOn (fun z : ℝ ↦ t ^ p * (t + z)⁻¹) (spectrum ℝ A) :=
    continuousOn_const.mul hg
  have hadd : ContinuousOn (fun z : ℝ ↦ t + z) (spectrum ℝ A) :=
    (continuous_const.add continuous_id).continuousOn
  have hcfc := cfc_sub (fun _ : ℝ ↦ t ^ (p - 1))
    (fun z : ℝ ↦ t ^ p * (t + z)⁻¹) A continuousOn_const hg_mul
  have hcfc_add :
      cfc (fun z : ℝ ↦ t + z) A = algebraMap ℝ (Matrix n n ℂ) t + A := by
    simpa only [id_eq, cfc_id' ℝ A hself] using
      cfc_const_add t (fun z : ℝ ↦ z) A continuous_id.continuousOn hself
  rw [hcfc, cfc_const _ _ hself, cfc_const_mul _ _ _ hg,
    cfc_inv _ _ hspectrum hadd hself, hcfc_add]
  simp only [Algebra.algebraMap_eq_smul_one, ← Matrix.nonsing_inv_eq_ringInverse]

/-- Equality of all positive shifted resolvents after a fixed matrix is applied
to their values on a vector implies the corresponding equality for positive
square roots.

This is the support-restricted form of the functional-calculus passage in
Jenčová--Ruskai, arXiv:0903.2895v4, lines 788--793. -/
theorem mulVec_sqrt_mulVec_eq_of_mulVec_resolvent_mulVec_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {S T : Matrix n n ℂ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {Q : Matrix n n ℂ} {x : n → ℂ}
    (hres : ∀ {t : ℝ}, 0 < t →
      Q *ᵥ ((t • (1 : Matrix n n ℂ) + S)⁻¹ *ᵥ x) =
        Q *ᵥ ((t • (1 : Matrix n n ℂ) + T)⁻¹ *ᵥ x)) :
    Q *ᵥ (CFC.sqrt S *ᵥ x) = Q *ᵥ (CFC.sqrt T *ᵥ x) := by
  let p : NNReal := 1 / 2
  have hp : (p : ℝ) ∈ Ioo 0 1 := by
    norm_num [p]
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
      (Matrix n n ℂ) hp
  have hSint := (hμ S hS.nonneg).1
  have hTint := (hμ T hT.nonneg).1
  have hintegrand : ∀ {t : ℝ}, 0 < t →
      Q *ᵥ (cfcₙ (Real.rpowIntegrand₀₁ p t) S *ᵥ x) =
        Q *ᵥ (cfcₙ (Real.rpowIntegrand₀₁ p t) T *ᵥ x) := by
    intro t ht
    have hSnonneg : (0 : Matrix n n ℂ) ≤ S := hS.nonneg
    have hTnonneg : (0 : Matrix n n ℂ) ≤ T := hT.nonneg
    have hcontS : ContinuousOn (Real.rpowIntegrand₀₁ (p : ℝ) t)
        (quasispectrum ℝ S) :=
      (Real.continuousOn_rpowIntegrand₀₁_Ici hp ht).mono
        (fun z hz ↦ quasispectrum_nonneg_of_nonneg S hSnonneg z hz)
    have hcontT : ContinuousOn (Real.rpowIntegrand₀₁ (p : ℝ) t)
        (quasispectrum ℝ T) :=
      (Real.continuousOn_rpowIntegrand₀₁_Ici hp ht).mono
        (fun z hz ↦ quasispectrum_nonneg_of_nonneg T hTnonneg z hz)
    rw [cfcₙ_eq_cfc hcontS, cfcₙ_eq_cfc hcontT,
      cfc_rpowIntegrand₀₁_eq_resolvent hS hp ht,
      cfc_rpowIntegrand₀₁_eq_resolvent hT hp ht]
    simp only [sub_mulVec, smul_mulVec, one_mulVec, mulVec_sub, mulVec_smul]
    rw [hres ht]
  have hAE :
      (fun t : ℝ ↦ Q *ᵥ (cfcₙ (Real.rpowIntegrand₀₁ p t) S *ᵥ x))
          =ᵐ[μ.restrict (Ioi 0)]
        fun t : ℝ ↦ Q *ᵥ (cfcₙ (Real.rpowIntegrand₀₁ p t) T *ᵥ x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hintegrand ht
  let L : Matrix n n ℂ →L[ℂ] (n → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M ↦ Q *ᵥ (M *ᵥ x)
        map_add' := by
          intro M N
          rw [add_mulVec, mulVec_add]
        map_smul' := by
          intro c M
          rw [smul_mulVec, mulVec_smul]
          rfl }
  rw [CFC.sqrt_eq_nnrpow, CFC.sqrt_eq_nnrpow,
    show (1 / 2 : NNReal) = p by rfl,
    (hμ S hS.nonneg).2, (hμ T hT.nonneg).2]
  change L (∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ p t) S ∂μ) =
    L (∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ p t) T ∂μ)
  rw [← L.integral_comp_comm hSint, ← L.integral_comp_comm hTint]
  exact integral_congr_ae hAE

/-- Equality of all positive shifted resolvents on a fixed vector implies
equality of the positive square roots on that vector.

Jenčová--Ruskai, arXiv:0903.2895v4, lines 658–680, obtains the corresponding
functional-calculus conclusion from analytic continuation and the Cauchy
integral formula. Here the same positive-square-root specialization is proved
with the Löwner integral representation of the real power `p = 1 / 2`. -/
theorem sqrt_mulVec_eq_of_resolvent_mulVec_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {S T : Matrix n n ℂ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    {x : n → ℂ}
    (hres : ∀ {t : ℝ}, 0 < t →
      (t • (1 : Matrix n n ℂ) + S)⁻¹ *ᵥ x =
        (t • (1 : Matrix n n ℂ) + T)⁻¹ *ᵥ x) :
    CFC.sqrt S *ᵥ x = CFC.sqrt T *ᵥ x := by
  have hresOne : ∀ {t : ℝ}, 0 < t →
      (1 : Matrix n n ℂ) *ᵥ ((t • 1 + S)⁻¹ *ᵥ x) =
        (1 : Matrix n n ℂ) *ᵥ ((t • 1 + T)⁻¹ *ᵥ x) := by
    intro t ht
    simpa only [one_mulVec] using hres ht
  simpa only [one_mulVec] using
    mulVec_sqrt_mulVec_eq_of_mulVec_resolvent_mulVec_eq hS hT hresOne

/-- The source-`B` left-right resolvent is the shifted resolvent of the
relative modular Kronecker matrix on the vectorized identity.

This is the finite-dimensional factorization in Jenčová--Ruskai,
arXiv:0903.2895v4, lines 661–670. -/
theorem sourceB_resolvent_eq_relativeModular
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 < t) :
    (A ⊗ₖ (1 : Matrix n n ℂ) +
        t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ))⁻¹ *ᵥ Matrix.vec Bᵀ =
      (t • (1 : Matrix (n × n) (n × n) ℂ) +
        A ⊗ₖ (B⁻¹)ᵀ)⁻¹ *ᵥ
          Matrix.vec (1 : Matrix n n ℂ)ᵀ := by
  let cMat : Matrix (n × n) (n × n) ℂ :=
    (1 : Matrix n n ℂ) ⊗ₖ Bᵀ
  let delta : Matrix (n × n) (n × n) ℂ := A ⊗ₖ (B⁻¹)ᵀ
  let res : Matrix (n × n) (n × n) ℂ := t • 1 + delta
  have hC : cMat.PosDef := by
    exact Matrix.PosDef.one.kronecker hB.transpose
  have hΔ : delta.PosDef := by
    exact hA.kronecker hB.inv.transpose
  have hR : res.PosDef := by
    exact (Matrix.PosDef.one.smul ht).add hΔ
  letI : Invertible B := hB.isUnit.invertible
  letI : Invertible cMat := hC.isUnit.invertible
  letI : Invertible res := hR.isUnit.invertible
  have hBT : Bᵀ * (B⁻¹)ᵀ = (1 : Matrix n n ℂ) := by
    rw [← Matrix.transpose_mul, inv_mul_of_invertible, Matrix.transpose_one]
  have hCΔ : cMat * delta = A ⊗ₖ (1 : Matrix n n ℂ) := by
    dsimp only [cMat, delta]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, hBT]
  have hfactor : cMat * res =
      A ⊗ₖ (1 : Matrix n n ℂ) +
        t • ((1 : Matrix n n ℂ) ⊗ₖ Bᵀ) := by
    dsimp only [res]
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hCΔ]
    dsimp only [cMat]
    abel
  have hb : cMat *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ = Matrix.vec Bᵀ := by
    dsimp only [cMat]
    rw [Matrix.kronecker_mulVec_vec]
    simp
  rw [← hfactor, ← hb, Matrix.mul_inv_rev, mulVec_mulVec,
    Matrix.mul_assoc, inv_mul_of_invertible, Matrix.mul_one]

/-- The positive square root of the relative modular Kronecker matrix, applied
to the vectorized identity, is the vectorization of the square-root ratio.

This is the positive-definite square-root specialization of the functional
calculus conclusion in Jenčová--Ruskai, arXiv:0903.2895v4, lines 675–680. -/
theorem relativeModular_sqrt_mulVec_vec_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    CFC.sqrt (A ⊗ₖ (B⁻¹)ᵀ) *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ =
      Matrix.vec (CFC.sqrt A * (CFC.sqrt B)⁻¹)ᵀ := by
  let qA : Matrix n n ℂ := CFC.sqrt A
  let qB : Matrix n n ℂ := CFC.sqrt B
  let delta : Matrix (n × n) (n × n) ℂ := A ⊗ₖ (B⁻¹)ᵀ
  let qDelta : Matrix (n × n) (n × n) ℂ := qA ⊗ₖ (qB⁻¹)ᵀ
  have hqA : qA.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hqB : qB.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hdelta : delta.PosDef := hA.kronecker hB.inv.transpose
  have hqDelta : qDelta.PosSemidef :=
    hqA.kronecker hqB.inv.transpose
  have hqA_sq : qA * qA = A := by
    simpa only [qA] using CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hqB_sq : qB * qB = B := by
    simpa only [qB] using CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  have hqBunit : IsUnit qB := by
    apply (CFC.isUnit_sqrt_iff B hB.posSemidef.nonneg).2
    exact hB.isUnit
  letI : Invertible qB := hqBunit.invertible
  have hqB_inv_sq : qB⁻¹ * qB⁻¹ = B⁻¹ := by
    rw [← Matrix.mul_inv_rev, hqB_sq]
  have hqDelta_sq : qDelta * qDelta = delta := by
    dsimp only [qDelta, delta]
    rw [← Matrix.mul_kronecker_mul, hqA_sq, ← Matrix.transpose_mul,
      hqB_inv_sq]
  have hsqrt : CFC.sqrt delta = qDelta := by
    apply (CFC.sqrt_eq_iff delta qDelta hdelta.posSemidef.nonneg
      hqDelta.nonneg).2
    exact hqDelta_sq
  change CFC.sqrt delta *ᵥ Matrix.vec (1 : Matrix n n ℂ)ᵀ =
    Matrix.vec (qA * qB⁻¹)ᵀ
  rw [hsqrt]
  dsimp only [qDelta]
  rw [Matrix.kronecker_mulVec_vec]
  simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.transpose_mul]

end Matrix
