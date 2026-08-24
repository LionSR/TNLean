/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Existence
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.SharedInfra.BlockGauge
import TNLean.MPS.SharedInfra.CoisometryGauge

/-!
# Gauge normalization from CPSV canonical form to canonical form II

A tensor in the literal canonical form of Cirac--Pérez-García--Schuch--Verstraete
admits a canonical-form-II representative in the same ambient bond dimension.
Each retained normal block is first put in its Perron trace-preserving gauge and
then unitarily diagonalized.  The resulting block gauges are assembled on the
retained direct sum.  If `U` is the ambient coisometry, the retained gauge `X`
is extended across the omitted zero coordinates by

`Uᴴ * X * U + (1 - Uᴴ * U)`.

This is the nonsingular gauge asserted in arXiv:1606.00608, Appendix A,
lines 1058--1077 and eq. `II_XAX`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

private structure CFIIBlockGaugeData {m : ℕ} (A : MPSTensor d m) where
  block : MPSTensor d m
  gauge : GaugeEquiv A block
  normal : IsNormalTensor block
  leftCanonical : IsLeftCanonical block
  fixedPoint : ∃ Λ : Matrix (Fin m) (Fin m) ℂ,
    Λ.PosDef ∧ Λ.IsDiag ∧ Kraus.transferMap block Λ = Λ

private theorem IsNormalTensor.exists_cfiiBlockGaugeData {m : ℕ} [NeZero m]
    {A : MPSTensor d m} (hA : IsNormalTensor A) :
    Nonempty (CFIIBlockGaugeData A) := by
  obtain ⟨σ, _hσ, _hσfix, hTP, hGaugeTP, _hPrimitive, hIrreducible⟩ :=
    hA.exists_tpGauge
  let T : MPSTensor d m := tpGauge A σ
  obtain ⟨V, Λ, _hSame, hΛPos, hΛDiag, hLeft, hΛFix⟩ :=
    exists_CFII_data_of_TP_of_isIrreducibleTensor T hTP hIrreducible (NeZero.pos m)
  let B : MPSTensor d m := fun i =>
    (V : Matrix (Fin m) (Fin m) ℂ)ᴴ * T i * (V : Matrix (Fin m) (Fin m) ℂ)
  have hGaugeUnitary : GaugeEquiv T B := by
    refine ⟨(unitaryGL V)⁻¹, fun i => ?_⟩
    simp [B, unitaryGL]
  have hGauge : GaugeEquiv A B := hGaugeTP.trans hGaugeUnitary
  have hNormalAlg : Kraus.IsNormal B :=
    isNormal_of_gaugeEquiv hA.isNormal hGauge
  have hNormal : IsNormalTensor B :=
    isNormalTensor_of_isNormal_leftCanonical B hNormalAlg hLeft
  exact ⟨⟨B, hGauge, hNormal, hLeft, Λ, hΛPos, hΛDiag, hΛFix⟩⟩

/-- For literal CPSV canonical-form data, there are canonical-form-II witness
data in the same ambient bond dimension, related to the original tensor by a
nonsingular gauge. The returned witness records that the total retained block
dimension is unchanged by the blockwise gauges.

Source: arXiv:1606.00608, Appendix A, lines 1058--1077 and eq. `II_XAX`. -/
theorem CPSVCanonicalFormData.exists_gaugeEquiv_canonicalFormIIData
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) :
    ∃ (B : MPSTensor d D) (dataB : CPSVCanonicalFormIIData B),
      GaugeEquiv A B ∧
        ∑ k : Fin dataB.r, dataB.dim k = ∑ k : Fin data.r, data.dim k := by
  classical
  let blockData : (k : Fin data.r) → CFIIBlockGaugeData (data.blocks k) := fun k => by
    letI : NeZero (data.dim k) := NeZero.of_pos (data.dim_pos k)
    exact Classical.choice
      (IsNormalTensor.exists_cfiiBlockGaugeData (A := data.blocks k)
        (m := data.dim k) (hA := data.blocks_normal k))
  let newBlocks : (k : Fin data.r) → MPSTensor d (data.dim k) :=
    fun k => (blockData k).block
  let blockGauge : (k : Fin data.r) → GL (Fin (data.dim k)) ℂ :=
    fun k => Classical.choose (blockData k).gauge
  let X := globalGaugeOfBlocks blockGauge
  let U := data.ambient_coisometry
  let G := coisometryExtendGL U data.coisometric X
  let B : MPSTensor d D := fun i =>
    Uᴴ * toTensorFromBlocks data.weights newBlocks i * U
  have hBlockGauge : ∀ k i, newBlocks k i =
      (blockGauge k : Matrix (Fin (data.dim k)) (Fin (data.dim k)) ℂ) *
        data.blocks k i *
        (((blockGauge k)⁻¹ : GL (Fin (data.dim k)) ℂ) :
          Matrix (Fin (data.dim k)) (Fin (data.dim k)) ℂ) := by
    intro k
    exact Classical.choose_spec (blockData k).gauge
  have hDirect : ∀ i, toTensorFromBlocks data.weights newBlocks i =
      (X : Matrix (Fin (∑ k : Fin data.r, data.dim k))
        (Fin (∑ k : Fin data.r, data.dim k)) ℂ) *
        toTensorFromBlocks data.weights data.blocks i *
        (((X⁻¹ : GL (Fin (∑ k : Fin data.r, data.dim k)) ℂ)) :
          Matrix (Fin (∑ k : Fin data.r, data.dim k))
            (Fin (∑ k : Fin data.r, data.dim k)) ℂ) :=
    toTensorFromBlocks_eq_globalGaugeOfBlocks_conj
      data.weights data.blocks newBlocks blockGauge hBlockGauge
  have hGU : (G : Matrix (Fin D) (Fin D) ℂ) * Uᴴ =
      Uᴴ * (X : Matrix (Fin (∑ k : Fin data.r, data.dim k))
        (Fin (∑ k : Fin data.r, data.dim k)) ℂ) :=
    coisometryExtendGL_mul_conjTranspose U data.coisometric X
  have hUGinv : U * (((G⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) =
      (((X⁻¹ : GL (Fin (∑ k : Fin data.r, data.dim k)) ℂ)) :
        Matrix (Fin (∑ k : Fin data.r, data.dim k))
          (Fin (∑ k : Fin data.r, data.dim k)) ℂ) * U :=
    mul_coisometryExtendGL_inv U data.coisometric X
  have hGauge : GaugeEquiv A B := by
    refine ⟨G, fun i => ?_⟩
    rw [data.reconstruct i]
    let C := toTensorFromBlocks data.weights data.blocks i
    let Xmat : Matrix (Fin (∑ k : Fin data.r, data.dim k))
        (Fin (∑ k : Fin data.r, data.dim k)) ℂ := X
    let Xinv : Matrix (Fin (∑ k : Fin data.r, data.dim k))
        (Fin (∑ k : Fin data.r, data.dim k)) ℂ :=
      ((X⁻¹ : GL (Fin (∑ k : Fin data.r, data.dim k)) ℂ) : Matrix _ _ ℂ)
    let Gmat : Matrix (Fin D) (Fin D) ℂ := G
    let Ginv : Matrix (Fin D) (Fin D) ℂ :=
      ((G⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
    have hGU' : Gmat * Uᴴ = Uᴴ * Xmat := hGU
    have hUGinv' : U * Ginv = Xinv * U := hUGinv
    have hDirect' : toTensorFromBlocks data.weights newBlocks i = Xmat * C * Xinv :=
      hDirect i
    change Uᴴ * toTensorFromBlocks data.weights newBlocks i * U = _
    calc
      Uᴴ * toTensorFromBlocks data.weights newBlocks i * U =
          Uᴴ * (Xmat * C * Xinv) * U := by rw [hDirect']
      _ = (Uᴴ * Xmat) * C * (Xinv * U) := by simp only [Matrix.mul_assoc]
      _ = (Gmat * Uᴴ) * C * (U * Ginv) := by rw [hGU', hUGinv']
      _ = Gmat * (Uᴴ * C * U) * Ginv := by simp only [Matrix.mul_assoc]
  let dataB : CPSVCanonicalFormIIData B := {
      r := data.r
      dim := data.dim
      dim_pos := data.dim_pos
      weights := data.weights
      weights_ne_zero := data.weights_ne_zero
      blocks := newBlocks
      blocks_normal := fun k => (blockData k).normal
      total_dim_le := data.total_dim_le
      ambient_coisometry := U
      coisometric := data.coisometric
      reconstruct := fun _ => rfl
      blocks_left_canonical := fun k => (blockData k).leftCanonical
      blocks_fixed_point := fun k => (blockData k).fixedPoint }
  exact ⟨B, dataB, hGauge, rfl⟩

/-- For literal CPSV canonical-form data, there is a canonical-form-II
representative in the same ambient bond dimension, related to the original
tensor by a nonsingular gauge.

Source: arXiv:1606.00608, Appendix A, lines 1058--1077 and eq. `II_XAX`. -/
theorem CPSVCanonicalFormData.exists_gaugeEquiv_canonicalFormII
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) :
    ∃ B : MPSTensor d D, GaugeEquiv A B ∧ IsCPSVCanonicalFormII B := by
  obtain ⟨B, dataB, hGauge, _⟩ := data.exists_gaugeEquiv_canonicalFormIIData
  exact ⟨B, hGauge, dataB.isCPSVCanonicalFormII⟩

/-- Every tensor in literal CPSV canonical form is gauge-equivalent, in the
same ambient bond dimension, to a tensor in literal canonical form II.

Source: arXiv:1606.00608, Appendix A, lines 1058--1077 and eq. `II_XAX`. -/
theorem IsCPSVCanonicalForm.exists_gaugeEquiv_canonicalFormII
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    ∃ B : MPSTensor d D, GaugeEquiv A B ∧ IsCPSVCanonicalFormII B := by
  obtain ⟨B, hGauge, dataB⟩ := hA.data.exists_gaugeEquiv_canonicalFormII
  exact ⟨B, hGauge, dataB⟩

end MPSTensor
