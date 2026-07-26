/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Existence
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.SharedInfra.BlockGauge

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

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Extend an invertible operator on the range of a coisometry by the identity
on the orthogonal complement of its initial space. -/
noncomputable def coisometryExtendGL {r n : ℕ}
    (U : Matrix (Fin r) (Fin n) ℂ) (hU : U * Uᴴ = 1) (X : GL (Fin r) ℂ) :
    GL (Fin n) ℂ := by
  let P : Matrix (Fin n) (Fin n) ℂ := Uᴴ * U
  let Q : Matrix (Fin n) (Fin n) ℂ := 1 - P
  let G : Matrix (Fin n) (Fin n) ℂ := Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) * U + Q
  let H : Matrix (Fin n) (Fin n) ℂ :=
    Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) * U + Q
  have hUQ : U * Q = 0 := by
    simp only [Q, P, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU,
      Matrix.one_mul, sub_self]
  have hQU : Q * Uᴴ = 0 := by
    simp only [Q, P, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU,
      Matrix.mul_one, sub_self]
  have hQQ : Q * Q = Q := by
    simp only [Q, P]
    calc
      (1 - Uᴴ * U) * (1 - Uᴴ * U) =
          1 - Uᴴ * U - Uᴴ * U + Uᴴ * (U * Uᴴ) * U := by noncomm_ring
      _ = 1 - Uᴴ * U := by rw [hU]; simp
  have hGH : G * H = 1 := by
    simp only [G, H, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [hU, Matrix.one_mul, hUQ, Matrix.mul_zero, hQU, Matrix.zero_mul, hQQ]
    simp
  have hHG : H * G = 1 := by
    simp only [G, H, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [hU, Matrix.one_mul, hUQ, Matrix.mul_zero, hQU, Matrix.zero_mul, hQQ]
    simp
  exact ⟨G, H, hGH, hHG⟩

@[simp] theorem coisometryExtendGL_val {r n : ℕ}
    (U : Matrix (Fin r) (Fin n) ℂ) (hU : U * Uᴴ = 1) (X : GL (Fin r) ℂ) :
    (coisometryExtendGL U hU X : Matrix (Fin n) (Fin n) ℂ) =
      Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) * U + (1 - Uᴴ * U) := by
  rfl

@[simp] theorem coisometryExtendGL_inv_val {r n : ℕ}
    (U : Matrix (Fin r) (Fin n) ℂ) (hU : U * Uᴴ = 1) (X : GL (Fin r) ℂ) :
    (((coisometryExtendGL U hU X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) * U +
        (1 - Uᴴ * U) := by
  rfl

private structure CFIIBlockGaugeData {m : ℕ} (A : MPSTensor d m) where
  block : MPSTensor d m
  gauge : GaugeEquiv A block
  normal : IsNormalTensor block
  leftCanonical : IsLeftCanonical block
  fixedPoint : ∃ Λ : Matrix (Fin m) (Fin m) ℂ,
    Λ.PosDef ∧ Λ.IsDiag ∧ transferMap block Λ = Λ

private theorem IsNormalTensor.exists_cfiiBlockGaugeData {m : ℕ} [NeZero m]
    {A : MPSTensor d m} (hA : IsNormalTensor A) :
    Nonempty (CFIIBlockGaugeData A) := by
  obtain ⟨σ, _hσ, _hσfix, hTP, hGaugeTP, _hPrimitive, hIrreducible⟩ :=
    hA.exists_tpGauge
  let T : MPSTensor d m := tpGauge A σ
  obtain ⟨V, Λ, hSame, hΛPos, hΛDiag, hLeft, hΛFix⟩ :=
    exists_CFII_data_of_TP_of_isIrreducibleTensor T hTP hIrreducible (NeZero.pos m)
  let B : MPSTensor d m := fun i =>
    (V : Matrix (Fin m) (Fin m) ℂ)ᴴ * T i * (V : Matrix (Fin m) (Fin m) ℂ)
  have hGaugeUnitary : GaugeEquiv T B := by
    refine ⟨(unitaryGL V)⁻¹, fun i => ?_⟩
    simp [B, unitaryGL]
  have hGauge : GaugeEquiv A B := hGaugeTP.trans hGaugeUnitary
  have hNormalAlg : IsNormal B :=
    isNormal_of_gaugeEquiv hA.isNormal hGauge
  have hNormal : IsNormalTensor B :=
    isNormalTensor_of_isNormal_leftCanonical B hNormalAlg hLeft
  exact ⟨⟨B, hGauge, hNormal, hLeft, Λ, hΛPos, hΛDiag, hΛFix⟩⟩

/-- Literal CPSV canonical-form data admit a canonical-form-II representative
in the same ambient bond dimension, related to the original tensor by a
nonsingular gauge.

Source: arXiv:1606.00608, Appendix A, lines 1058--1077 and eq. `II_XAX`. -/
theorem CPSVCanonicalFormData.exists_gaugeEquiv_canonicalFormII
    {A : MPSTensor d D} (data : CPSVCanonicalFormData A) :
    ∃ B : MPSTensor d D, GaugeEquiv A B ∧ CPSVCanonicalFormIIData B := by
  classical
  let blockData : (k : Fin data.r) → CFIIBlockGaugeData (data.blocks k) := fun k =>
    @Classical.choice _
      (IsNormalTensor.exists_cfiiBlockGaugeData (A := data.blocks k)
        (m := data.dim k) (hA := data.blocks_normal k)
        (NeZero.of_pos (data.dim_pos k)))
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
        (Fin (∑ k : Fin data.r, data.dim k)) ℂ) := by
    simp [G, U, Matrix.mul_assoc, data.coisometric]
  have hUGinv : U * (((G⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) =
      (((X⁻¹ : GL (Fin (∑ k : Fin data.r, data.dim k)) ℂ)) :
        Matrix (Fin (∑ k : Fin data.r, data.dim k))
          (Fin (∑ k : Fin data.r, data.dim k)) ℂ) * U := by
    simp [G, U, Matrix.mul_assoc, data.coisometric]
  have hGauge : GaugeEquiv A B := by
    refine ⟨G, fun i => ?_⟩
    rw [data.reconstruct i]
    simp only [B, hDirect i, Matrix.mul_assoc, hGU, hUGinv]
  refine ⟨B, hGauge, ?_⟩
  refine
    { r := data.r
      dim := data.dim
      dim_pos := data.dim_pos
      weights := data.weights
      blocks := newBlocks
      blocks_normal := fun k => (blockData k).normal
      total_dim_le := data.total_dim_le
      ambient_coisometry := U
      coisometric := data.coisometric
      reconstruct := fun _ => rfl
      blocks_left_canonical := fun k => (blockData k).leftCanonical
      blocks_fixed_point := fun k => (blockData k).fixedPoint }

/-- Every tensor in literal CPSV canonical form is gauge-equivalent, in the
same ambient bond dimension, to a tensor in literal canonical form II.

Source: arXiv:1606.00608, Appendix A, lines 1058--1077 and eq. `II_XAX`. -/
theorem IsCPSVCanonicalForm.exists_gaugeEquiv_canonicalFormII
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    ∃ B : MPSTensor d D, GaugeEquiv A B ∧ IsCPSVCanonicalFormII B := by
  obtain ⟨B, hGauge, dataB⟩ := hA.data.exists_gaugeEquiv_canonicalFormII
  exact ⟨B, hGauge, dataB.isCPSVCanonicalFormII⟩

end MPSTensor
