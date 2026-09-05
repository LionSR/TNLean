/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinSumPermutation
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.Chain.CrossProductRigidity
import TNLean.MPS.MPU.PhysicalAdjointCanonicalForm
import TNLean.MPS.MPU.SourceFactorContraction
import TNLean.MPS.MPU.SuppliedFixedWitnesses

/-!
# The adjoint-simple six-tensor contraction

The six-tensor argument in arXiv:2502.20257, lines 1164--1254, removes
one double-layer letter at a canonical boundary. We align the simplicity
witnesses with the recorded fixed matrix, expand the six-tensor network,
and reduce it in two ways to prove the cross-product identity for the actual
marked three-tensor contraction. Normality then implies proportionality by
the existing cross-product rigidity theorem (source lines 1255--1325).
The source's additional assumption that the physical adjoint is simple is
retained explicitly.

All double-layer letters and the marked contraction are raw MPO tensors.
The transfer power used to align their boundary witnesses uses the normalized
flattening. For rigidity we scale the cross-product identity to that normalized
flattening, then absorb its scalar into the proportionality constant. We do not
identify raw and normalized normality by definitional equality.

This file does not prove the four normalized source-factor equations
`eq:MPUnice3` and `eq:MPUnice4`.
-/

open scoped Matrix BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ}

/-- Removal of a boundary letter in a pair of double-layer letters, with the
canonical left boundary \(I\) and right boundary \(\rho\).

These are the local boundary contractions needed in arXiv:2502.20257,
lines 1164--1254. For the reflected pair, transport the canonical data to
the physical adjoint and separately supply its simplicity; simplicity
of the original tensor is not used as a substitute for that hypothesis.
The witness alignment uses arXiv:1703.09188, equations `Erightleft`,
`simple1`, and `simple2`.
-/
theorem IsMPUCanonicalFormII.doubleLayer_boundary_contractions
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) :
    let Φ : Fin (D * D) → ℂ := fun x ↦
      (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)
    let ρ : Fin (D * D) → ℂ := fun x ↦ hU.ρ.vec (finProdFinEquiv.symm x)
    ∀ i j k l : Fin d,
      Matrix.vecMul Φ (doubleLayerTensor U i j * doubleLayerTensor U k l) =
        (if i = j then (1 : ℂ) else 0) • Matrix.vecMul Φ (doubleLayerTensor U k l) ∧
      (doubleLayerTensor U i j * doubleLayerTensor U k l) *ᵥ ρ =
        (if k = l then (1 : ℂ) else 0) • (doubleLayerTensor U i j *ᵥ ρ) := by
  have := hU.neZero_phys
  dsimp only
  let Φ : Fin (D * D) → ℂ := fun x ↦
    (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)
  let ρ : Fin (D * D) → ℂ := fun x ↦ hU.ρ.vec (finProdFinEquiv.symm x)
  have h₂ := hsimple.simple2_of_normalizedDiagonal_pow_eq_vecMulVec
    ρ Φ (max (D * D - 1) 1) (by omega) hU.normalizedDiagonal_pow_eq_vecMulVec
  have h₁ := hU.isMPU.simple1_of_simple2_supplied Φ ρ h₂
  intro i j k l
  change Matrix.vecMul Φ (_ * _) = _ • Matrix.vecMul Φ _ ∧
    (_ * _) *ᵥ ρ = _ • (_ *ᵥ ρ)
  rw [h₂ i j k l]
  constructor
  · rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      Matrix.vecMul_vecMulVec, ← Matrix.dotProduct_mulVec, h₁ i j,
      Matrix.smul_vecMul]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.vecMulVec_mulVec, h₁ k l, Matrix.mulVec_smul]
    split_ifs <;> simp

/-- Physical adjunction preserves the canonical data with exactly the same
recorded diagonal matrix \(\rho\). This supplies the canonical boundaries for
the reflected double layer in arXiv:2502.20257, lines 1164--1254. It makes
no claim that physical adjunction preserves simplicity.
-/
noncomputable def IsMPUCanonicalFormII.physicalAdjointTensor
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U) :
    IsMPUCanonicalFormII (MPOTensor.physicalAdjointTensor U) where
  isMPU := hU.isMPU.physicalAdjointTensor
  cfii := hU.cfii.physicalAdjointNormalizedFlattening
  fullSupport_eq := hU.fullSupport_eq
  ρ := hU.ρ
  ρ_posDef := hU.ρ_posDef
  ρ_isDiag := hU.ρ_isDiag
  ρ_trace := hU.ρ_trace
  ρ_fixed := by
    rw [normalizedFlattening_physicalAdjointTensor,
      MPSTensor.transferMap_reindexPhysical_equiv]
    rw [← MPSTensor.map_star_eq_self_of_posDef_isDiag hU.ρ_posDef hU.ρ_isDiag,
      MPSTensor.transferMap_mapStar, hU.ρ_fixed,
      MPSTensor.map_star_eq_self_of_posDef_isDiag hU.ρ_posDef hU.ρ_isDiag]

/-- The reflected double layer admits canonical boundary removal using the
same \(I,\rho\) boundaries. The adjoint-simple hypothesis is the explicit
additional source hypothesis of arXiv:2502.20257, Proposition `eq:MPUnice3`--
`eq:MPUnice4`, lines 1070--1163; the contraction is used in lines 1164--1254.
-/
theorem IsMPUCanonicalFormII.physicalAdjoint_doubleLayer_boundary_contractions
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) :
    let V := MPOTensor.physicalAdjointTensor U
    let Φ : Fin (D * D) → ℂ := fun x ↦
      (1 : Matrix (Fin D) (Fin D) ℂ).vec (finProdFinEquiv.symm x)
    let ρ : Fin (D * D) → ℂ := fun x ↦ hU.ρ.vec (finProdFinEquiv.symm x)
    ∀ i j k l : Fin d,
      Matrix.vecMul Φ (doubleLayerTensor V i j * doubleLayerTensor V k l) =
        (if i = j then (1 : ℂ) else 0) • Matrix.vecMul Φ (doubleLayerTensor V k l) ∧
      (doubleLayerTensor V i j * doubleLayerTensor V k l) *ᵥ ρ =
        (if k = l then (1 : ℂ) else 0) • (doubleLayerTensor V i j *ᵥ ρ) :=
  hU.physicalAdjointTensor.doubleLayer_boundary_contractions hadjoint

private theorem sum_doubled_bond (f : Fin (D * D) → ℂ) :
    (∑ z, f z) = ∑ x : Fin D, ∑ y : Fin D, f (finProdFinEquiv (x, y)) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]

private theorem upper_boundary_entries
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U))
    (i j k l : Fin d) (b r : Fin D) :
    (∑ x : Fin D, ∑ m : Fin D, ∑ n : Fin D,
      (∑ p : Fin d, U i p x m * star (U j p x n)) *
        (∑ q : Fin d, U k q m b * star (U l q n r))) =
      (if i = j then (1 : ℂ) else 0) *
        ∑ x : Fin D, ∑ q : Fin d, U k q x b * star (U l q x r) := by
  have h := congrArg (fun v ↦ v (finProdFinEquiv (b, r)))
    ((hU.physicalAdjoint_doubleLayer_boundary_contractions hadjoint i j k l).1)
  simpa [Matrix.vecMul, dotProduct, Matrix.mul_apply, sum_doubled_bond,
    Matrix.vec, Matrix.one_apply, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul] using h

private theorem lower_boundary_entries
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (i j k l : Fin d) (x a : Fin D) :
    (∑ r : Fin D, ∑ t : Fin D, ∑ n : Fin D, ∑ z : Fin D,
      (∑ p : Fin d, star (U p i x n) * U p j a z) *
        (∑ q : Fin d, star (U q k n r) * U q l z t) * hU.ρ t r) =
      (if k = l then (1 : ℂ) else 0) *
        ∑ r : Fin D, ∑ t : Fin D,
          (∑ p : Fin d, star (U p i x r) * U p j a t) * hU.ρ t r := by
  have h := congrArg (fun v ↦ v (finProdFinEquiv (x, a)))
    ((hU.doubleLayer_boundary_contractions hsimple i j k l).2)
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, sum_doubled_bond,
    Matrix.vec, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul] using h

/-- The marked three-tensor contraction \(s\) in arXiv:2502.20257,
lines 1190--1218. Its left open bond is on the bottom tensor and its right
open bond on the top tensor. The entry \(\rho_{tr}\) follows the vectorization
order of the middle/bottom right boundary. There is no physical-dimension
normalization factor: these are raw MPO letters. Explicitly,
\[
  s^{ij}_{ab}=\sum_{p,q,x,r,t} U^{ip}_{xb}\,
    \overline{U^{qp}_{xr}}\,U^{qj}_{at}\,\rho_{tr}.
\]
For diagonal \(\rho\), the only surviving terms have \(t=r\), as in the
source diagram. -/
noncomputable def adjointSimpleContraction (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : MPOTensor d D :=
  fun i j a b ↦ ∑ p : Fin d, ∑ x : Fin D, ∑ r : Fin D, ∑ t : Fin D,
    U i p x b * (∑ q : Fin d, star (U q p x r) * U q j a t) * ρ t r

private noncomputable def sixTensorContraction (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (i j k l : Fin d) (a b : Fin D) : ℂ :=
  ∑ p : Fin d, ∑ x : Fin D, ∑ q : Fin d, ∑ m : Fin D,
    (U i p x m * U k q m b) *
      (∑ r : Fin D, ∑ t : Fin D, ∑ n : Fin D, ∑ z : Fin D,
        (∑ v : Fin d, star (U v p x n) * U v j a z) *
          (∑ w : Fin d, star (U w q n r) * U w l z t) * ρ t r)

private theorem sixTensorContraction_lower
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U) (i j k l : Fin d) (a b : Fin D) :
    sixTensorContraction U hU.ρ i j k l a b =
      (adjointSimpleContraction U hU.ρ i j * U k l) a b := by
  simp only [sixTensorContraction, lower_boundary_entries hU hsimple]
  simp only [mul_ite, one_mul, mul_zero, mul_assoc, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm, Fintype.sum_reverse_three]
  simp only [Matrix.mul_apply, adjointSimpleContraction,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  funext m
  apply Finset.sum_congr₂
  intro p _ x _
  apply Finset.sum_congr₂
  intro r _ t _
  apply Finset.sum_congr rfl
  intro v _
  ring

private theorem sixTensorContraction_reorder (U : MPOTensor d D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (i j k l : Fin d) (a b : Fin D) :
    sixTensorContraction U ρ i j k l a b =
      ∑ v : Fin d, ∑ w : Fin d, ∑ z : Fin D, ∑ t : Fin D, ∑ r : Fin D,
        (U v j a z * U w l z t * ρ t r) *
          (∑ x : Fin D, ∑ m : Fin D, ∑ n : Fin D,
            (∑ p : Fin d, U i p x m * star (U v p x n)) *
              (∑ q : Fin d, U k q m b * star (U w q n r))) := by
  simp only [sixTensorContraction, Finset.mul_sum, Finset.sum_mul]
  let e :
      (Fin d × Fin D × Fin d × Fin D × Fin D × Fin D × Fin D × Fin D × Fin d × Fin d) ≃
      (Fin d × Fin d × Fin D × Fin D × Fin D × Fin D × Fin D × Fin D × Fin d × Fin d) :=
    { toFun := fun ⟨p, x, q, m, r, t, n, z, w, v⟩ ↦ ⟨v, w, z, t, r, x, m, n, q, p⟩
      invFun := fun ⟨v, w, z, t, r, x, m, n, q, p⟩ ↦ ⟨p, x, q, m, r, t, n, z, w, v⟩
      left_inv := by rintro ⟨p, x, q, m, r, t, n, z, w, v⟩; rfl
      right_inv := by rintro ⟨v, w, z, t, r, x, m, n, q, p⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun ⟨p, x, q, m, r, t, n, z, w, v⟩ ↦
      (U i p x m * U k q m b) *
        ((star (U v p x n) * U v j a z) *
          (star (U w q n r) * U w l z t) * ρ t r))
    (fun ⟨v, w, z, t, r, x, m, n, q, p⟩ ↦
      (U v j a z * U w l z t * ρ t r) *
        ((U i p x m * star (U v p x n)) * (U k q m b * star (U w q n r))))
    (by rintro ⟨p, x, q, m, r, t, n, z, w, v⟩; dsimp [e]; ring)
  simpa only [Fintype.sum_prod_type] using h

private theorem sixTensorContraction_upper
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U))
    (i j k l : Fin d) (a b : Fin D) :
    sixTensorContraction U hU.ρ i j k l a b =
      (U i j * adjointSimpleContraction U hU.ρ k l) a b := by
  rw [sixTensorContraction_reorder]
  simp only [upper_boundary_entries hU hadjoint]
  simp only [mul_ite, one_mul, mul_zero, mul_assoc, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [Matrix.mul_apply, adjointSimpleContraction,
    Finset.mul_sum, Finset.sum_mul]
  let e : (Fin d × Fin D × Fin D × Fin D × Fin D × Fin d) ≃
      (Fin D × Fin d × Fin D × Fin D × Fin D × Fin d) :=
    { toFun := fun ⟨w, z, t, r, x, q⟩ ↦ ⟨z, q, x, r, t, w⟩
      invFun := fun ⟨z, q, x, r, t, w⟩ ↦ ⟨w, z, t, r, x, q⟩
      left_inv := by rintro ⟨w, z, t, r, x, q⟩; rfl
      right_inv := by rintro ⟨z, q, x, r, t, w⟩; rfl }
  have h := Fintype.sum_equiv e
    (fun ⟨w, z, t, r, x, q⟩ ↦
      (U i j a z * (U w l z t * hU.ρ t r)) *
        (U k q x b * star (U w q x r)))
    (fun ⟨z, q, x, r, t, w⟩ ↦
      U i j a z * (U k q x b * (star (U w q x r) * U w l z t) * hU.ρ t r))
    (by rintro ⟨w, z, t, r, x, q⟩; dsimp [e]; ring)
  simpa only [Fintype.sum_prod_type, mul_assoc] using h

/-- The two reductions of the six-tensor network give the cross-product
identity for the actual marked contraction \(s\). The upper pair uses the
left-boundary identity for the physical adjoint; the lower pair uses the
right-boundary identity for the original tensor.

Source: arXiv:2502.20257, lines 1164--1254. Both simplicity hypotheses are
retained, and no cross-product identity is assumed. -/
theorem IsMPUCanonicalFormII.adjointSimpleContraction_cross_mul
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U))
    (i j k l : Fin d) :
    adjointSimpleContraction U hU.ρ i j * U k l =
      U i j * adjointSimpleContraction U hU.ρ k l := by
  ext a b
  exact (sixTensorContraction_lower hU hsimple i j k l a b).symm.trans
    (sixTensorContraction_upper hU hadjoint i j k l a b)

/-- The marked contraction \(s\) is one common scalar multiple of the raw
MPU tensor. Apply normality rigidity to the normalized flattening after scaling
the proved cross-product equation, then absorb \(1/\sqrt d\) into the scalar.

Source: arXiv:2502.20257, lines 1255--1325. This is only the proportionality
step, not the subsequent determination of the normalized source-factor constants.
-/
theorem IsMPUCanonicalFormII.adjointSimpleContraction_eq_smul
    {U : MPOTensor d D} (hU : IsMPUCanonicalFormII U)
    (hsimple : IsMPUSimple U)
    (hadjoint : IsMPUSimple (MPOTensor.physicalAdjointTensor U)) :
    ∃ δ : ℂ, ∀ i j : Fin d, adjointSimpleContraction U hU.ρ i j = δ • U i j := by
  have := hU.neZero_phys
  have := hU.neZero_bond
  have hnormal : Kraus.IsNormal U.normalizedFlattening :=
    hU.isNormalTensor_normalizedFlattening.isNormal
  have hcross : ∀ i j : Fin (d * d),
      (adjointSimpleContraction U hU.ρ).toMPSTensor i * U.normalizedFlattening j =
        U.normalizedFlattening i * (adjointSimpleContraction U hU.ρ).toMPSTensor j := by
    intro i j
    simp only [normalizedFlattening, toMPSTensor, Matrix.mul_smul, Matrix.smul_mul]
    rw [hU.adjointSimpleContraction_cross_mul hsimple hadjoint]
  obtain ⟨δ, hδ⟩ := hnormal.eq_smul_of_cross_mul_eq hcross
  refine ⟨δ * ((Real.sqrt d : ℂ)⁻¹), ?_⟩
  intro i j
  simpa only [normalizedFlattening, toMPSTensor, MPSTensor.finProdFinEquiv_divNat,
    MPSTensor.finProdFinEquiv_modNat, smul_smul] using hδ (finProdFinEquiv (i, j))

end MPOTensor
