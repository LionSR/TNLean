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

open scoped Matrix BigOperators ComplexOrder

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
  have hPP : P * P = P := by
    simp only [P]
    calc
      (Uᴴ * U) * (Uᴴ * U) = Uᴴ * (U * Uᴴ) * U := by
        simp only [Matrix.mul_assoc]
      _ = Uᴴ * U := by rw [hU]; simp
  have hQQ : Q * Q = Q := by
    calc
      Q * Q = (1 - P) * (1 - P) := rfl
      _ = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPP]; abel
  have hGU : G * Uᴴ = Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) := by
    simp only [G, Matrix.add_mul, hQU, add_zero]
    calc
      (Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) * U) * Uᴴ =
          Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) * (U * Uᴴ) := by
            simp only [Matrix.mul_assoc]
      _ = Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) := by rw [hU, Matrix.mul_one]
  have hHU : H * Uᴴ =
      Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
    simp only [H, Matrix.add_mul, hQU, add_zero]
    calc
      (Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) * U) * Uᴴ =
          Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) *
            (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
        rw [hU, Matrix.mul_one]
  have hGQ : G * Q = Q := by
    simp only [G, Matrix.add_mul, hQQ, Matrix.mul_assoc, hUQ, Matrix.mul_zero]
    exact zero_add Q
  have hHQ : H * Q = Q := by
    simp only [H, Matrix.add_mul, hQQ, Matrix.mul_assoc, hUQ, Matrix.mul_zero]
    exact zero_add Q
  have hGH : G * H = 1 := by
    rw [show H = Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) * U + Q
      from rfl, Matrix.mul_add, hGQ]
    rw [← Matrix.mul_assoc G
      (Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))) U,
      ← Matrix.mul_assoc G Uᴴ, hGU]
    simp [Q, P, Matrix.mul_assoc]
  have hHG : H * G = 1 := by
    rw [show G = Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) * U + Q from rfl,
      Matrix.mul_add, hHQ]
    rw [← Matrix.mul_assoc H (Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ)) U,
      ← Matrix.mul_assoc H Uᴴ, hHU]
    simp [Q, P, Matrix.mul_assoc]
  exact ⟨G, H, hGH, hHG⟩

/-- The matrix underlying the extended gauge is the retained gauge plus the
identity on the orthogonal complement. -/
@[simp] theorem coisometryExtendGL_val {r n : ℕ}
    (U : Matrix (Fin r) (Fin n) ℂ) (hU : U * Uᴴ = 1) (X : GL (Fin r) ℂ) :
    (coisometryExtendGL U hU X : Matrix (Fin n) (Fin n) ℂ) =
      Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) * U + (1 - Uᴴ * U) := by
  rfl

/-- The inverse extended gauge is obtained by extending the inverse retained gauge. -/
@[simp] theorem coisometryExtendGL_inv_val {r n : ℕ}
    (U : Matrix (Fin r) (Fin n) ℂ) (hU : U * Uᴴ = 1) (X : GL (Fin r) ℂ) :
    (((coisometryExtendGL U hU X)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Uᴴ * (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) * U +
        (1 - Uᴴ * U) := by
  rfl

/-- The extended gauge acts on the retained coisometric inclusion as the
original retained-space gauge. -/
theorem coisometryExtendGL_mul_conjTranspose {r n : ℕ}
    (U : Matrix (Fin r) (Fin n) ℂ) (hU : U * Uᴴ = 1) (X : GL (Fin r) ℂ) :
    (coisometryExtendGL U hU X : Matrix (Fin n) (Fin n) ℂ) * Uᴴ =
      Uᴴ * (X : Matrix (Fin r) (Fin r) ℂ) := by
  rw [coisometryExtendGL_val, Matrix.add_mul]
  have hComplement : (1 - Uᴴ * U) * Uᴴ = 0 := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one,
      sub_self]
  rw [hComplement, add_zero]
  simp only [Matrix.mul_assoc, hU, Matrix.mul_one]

/-- The coisometry intertwines the inverse extended gauge with the inverse
retained-space gauge. -/
theorem mul_coisometryExtendGL_inv {r n : ℕ}
    (U : Matrix (Fin r) (Fin n) ℂ) (hU : U * Uᴴ = 1) (X : GL (Fin r) ℂ) :
    U * (((coisometryExtendGL U hU X)⁻¹ : GL (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) =
      (((X⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) * U := by
  rw [coisometryExtendGL_inv_val, Matrix.mul_add]
  have hComplement : U * (1 - Uᴴ * U) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hU, Matrix.one_mul,
      sub_self]
  rw [hComplement, add_zero]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]

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
  obtain ⟨V, Λ, _hSame, hΛPos, hΛDiag, hLeft, hΛFix⟩ :=
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
    ∃ B : MPSTensor d D, GaugeEquiv A B ∧ IsCPSVCanonicalFormII B := by
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
  refine ⟨B, hGauge, ?_⟩
  refine ⟨{
      r := data.r
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
      blocks_fixed_point := fun k => (blockData k).fixedPoint }⟩

/-- Every tensor in literal CPSV canonical form is gauge-equivalent, in the
same ambient bond dimension, to a tensor in literal canonical form II.

Source: arXiv:1606.00608, Appendix A, lines 1058--1077 and eq. `II_XAX`. -/
theorem IsCPSVCanonicalForm.exists_gaugeEquiv_canonicalFormII
    {A : MPSTensor d D} (hA : IsCPSVCanonicalForm A) :
    ∃ B : MPSTensor d D, GaugeEquiv A B ∧ IsCPSVCanonicalFormII B := by
  obtain ⟨B, hGauge, dataB⟩ := hA.data.exists_gaugeEquiv_canonicalFormII
  exact ⟨B, hGauge, dataB⟩

end MPSTensor
