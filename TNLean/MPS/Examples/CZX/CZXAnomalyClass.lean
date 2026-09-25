/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ScalarThreeCocycleCyclicInvariant
import TNLean.MPS.Examples.CZX.CZXDecoratedFusion
import TNLean.MPS.Symmetry.MPOSymmetry.AssociatorToolkit

/-!
# The anomaly class of the decorated CZX representation

The decorated CZX matrix product unitary `U` of Garre-Rubio and Schuch
(arXiv:2405.00439, Section III.D) squares to the identity, so together with the
bond-one identity tensor it represents the group `ℤ₂`.  This file computes the
anomaly three-cochain `ω` of this representation, in the sense of
arXiv:2502.20257 (display preceding `eq:3-cocycle`), and shows that its
cohomology class is nontrivial for every choice of fusion tensors.

For the fusion tensors that are trivial whenever a factor is the identity and are
the printed pair `(V̂, V)` of arXiv:2405.00439, lines 1225--1244, for `(g, g)`,
the two fusion trees of the triple product of `g` agree up to the sign `-1`
against every nonempty word, so `ω(g,g,g) = -1`, while `ω(g,1,g) = 1`.  The
gauge-invariant product `ω(g,1,g) ω(g,g,g)` is therefore `-1`, for every choice
of fusion tensors.

## Main definitions

* `CZXCompression.czxFamily`: the `ℤ₂`-indexed family `1 ↦ δ`, `g ↦ U`.
* `CZXCompression.czxFusionData`: the fusion tensors described above.

## Main results

* `CZXCompression.czxFamily_isNormalRepresentation`
* `CZXCompression.czxFusionData_omega_gen_gen_gen`: `ω(g,g,g) = -1`.
* `CZXCompression.cyclicInvariant_omega_czx`: `ω(g,1,g) ω(g,g,g) = -1` for every
  choice of fusion tensors.
* `CZXCompression.not_isTrivialGaugeClass_omega_czx`: the anomaly class is
  nontrivial for every choice of fusion tensors.
-/

noncomputable section

open scoped Matrix Kronecker
open TNLean.Algebra MPOTensor MPSTensor

namespace CZXCompression

/-! ### The family -/

/-- The bond dimension attached to a label of `ℤ₂`: one for the identity and two
for the generator. -/
def czxLabelBondDim (a : Fin 2) : ℕ := if a = 0 then 1 else 2

/-- The tensor attached to a label of `ℤ₂`: the bond-one identity tensor for the
identity and the decorated CZX tensor for the generator. -/
def czxLabelTensor : (a : Fin 2) → MPOTensor 2 (czxLabelBondDim a)
  | ⟨0, _⟩ => MPOTensor.idTensor 2
  | ⟨1, _⟩ => czxDecoratedTensor
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- **The decorated CZX representation of `ℤ₂`**: the identity is represented by
the bond-one identity tensor and the generator by the decorated CZX tensor.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 412--428 (an MPU
of order two) and lines 1128--1180 (the decorated CZX tensor). -/
def czxFamily : GroupFamily (Multiplicative (Fin 2)) 2 where
  bondDim x := czxLabelBondDim x.toAdd
  bondDim_pos x := by unfold czxLabelBondDim; split <;> norm_num
  tensor x := czxLabelTensor x.toAdd

/-- The generator of `ℤ₂`, written multiplicatively. -/
def czxGen : Multiplicative (Fin 2) := Multiplicative.ofAdd 1

/-- The generator of `ℤ₂` has order two. -/
theorem czxGen_pow_two : czxGen ^ 2 = 1 := by decide

/-- The weight `δ_{s t}` of a letter of the pair alphabet is the weight of the letter
of the bond-one identity tensor. -/
private theorem pairDelta_eq (a : Fin (2 * 2)) :
    pairDelta a = if a.divNat = a.modNat then (1 : ℂ) else 0 := by
  fin_cases a <;> simp [pairDelta, pairDeltaInt, Fin.divNat, Fin.modNat]

/-- The product of two identity tensors is the identity tensor. -/
private theorem mulTensor_idTensor_idTensor :
    mulTensor (MPOTensor.idTensor 2) (MPOTensor.idTensor 2) =
      (MPOTensor.idTensor 2 : MPOTensor 2 (1 * 1)) := by
  rw [mulTensor_idTensor_left]
  rfl

/-! ### The representation -/

/-- **The decorated CZX tensors represent `ℤ₂` with normal tensors**: both tensors
are normal, and the periodic operators satisfy `δ δ = δ`, `δ U = U δ = U` and
`U U = δ` on every nonempty chain.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 412--428 and
1128--1181. -/
theorem czxFamily_isNormalRepresentation : czxFamily.IsNormalRepresentation where
  isNormal := Multiplicative.forall_zmod_two idTensor_isNormal czxDecoratedMPS_isNormal
  operator_mul := by
    refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_) <;> intro N hN
    · change mpo (MPOTensor.idTensor 2) N * mpo (MPOTensor.idTensor 2) N =
        mpo (MPOTensor.idTensor 2) N
      rw [mpo_idTensor, Matrix.one_mul]
    · change mpo (MPOTensor.idTensor 2) N * mpo czxDecoratedTensor N = mpo czxDecoratedTensor N
      rw [mpo_idTensor, Matrix.one_mul]
    · change mpo czxDecoratedTensor N * mpo (MPOTensor.idTensor 2) N = mpo czxDecoratedTensor N
      rw [mpo_idTensor, Matrix.mul_one]
    · change mpo czxDecoratedTensor N * mpo czxDecoratedTensor N = mpo (MPOTensor.idTensor 2) N
      have : NeZero N := ⟨by omega⟩
      rw [mpo_idTensor, mpo_czxDecoratedTensor_mul_self]

/-! ### The fusion tensors -/

/-- The left fusion tensors attached to a pair of labels: the identity when a
label is the identity, and the printed `V̂` for the pair of generators. -/
def czxLabelV : (a b : Fin 2) →
    Matrix (Fin (czxLabelBondDim (a + b))) (Fin (czxLabelBondDim a * czxLabelBondDim b)) ℂ
  | ⟨0, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨1, _⟩ => czxFusionVHat
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 2, h⟩ => absurd h (by omega)

/-- The right fusion tensors attached to a pair of labels: the identity when a
label is the identity, and the printed `V` for the pair of generators. -/
def czxLabelW : (a b : Fin 2) →
    Matrix (Fin (czxLabelBondDim a * czxLabelBondDim b)) (Fin (czxLabelBondDim (a + b))) ℂ
  | ⟨0, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 1) (Fin 1) ℂ)
  | ⟨0, _⟩, ⟨1, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨0, _⟩ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | ⟨1, _⟩, ⟨1, _⟩ => czxFusionV
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 2, h⟩ => absurd h (by omega)

/-- **Fusion tensors of the decorated CZX representation**: trivial whenever a
factor is the identity, and the printed pair `(V̂, V)` for two generators.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 426--477
(`eq:Ured`) with the fusion tensors of lines 1225--1244. -/
def czxFusionData : czxFamily.FusionData where
  V x y := czxLabelV x.toAdd y.toAdd
  W x y := czxLabelW x.toAdd y.toAdd
  isReduction := by
    refine Multiplicative.forall_zmod_two (Multiplicative.forall_zmod_two ?_ ?_)
      (Multiplicative.forall_zmod_two ?_ ?_)
    · change MPSTensor.IsReduction
        (mulTensor (MPOTensor.idTensor 2) (MPOTensor.idTensor 2)).toMPSTensor
        ((MPOTensor.idTensor 2 : MPOTensor 2 (1 * 1))).toMPSTensor 1 1
      exact MPSTensor.isReduction_one_one_of_eq (by rw [mulTensor_idTensor_idTensor])
    · change MPSTensor.IsReduction
        (mulTensor (MPOTensor.idTensor 2) czxDecoratedTensor).toMPSTensor
        ((czxDecoratedTensor : MPOTensor 2 (1 * 2))).toMPSTensor 1 1
      exact MPSTensor.isReduction_one_one_of_eq (by rw [mulTensor_idTensor_left]; rfl)
    · change MPSTensor.IsReduction
        (mulTensor czxDecoratedTensor (MPOTensor.idTensor 2)).toMPSTensor
        ((czxDecoratedTensor : MPOTensor 2 (2 * 1))).toMPSTensor 1 1
      exact MPSTensor.isReduction_one_one_of_eq (by rw [mulTensor_idTensor_right]; rfl)
    · change MPSTensor.IsReduction czxDecoratedSquare (MPOTensor.idTensor 2).toMPSTensor
        czxFusionVHat czxFusionV
      refine ⟨czxFusionVHat_mul_czxFusionV, fun w ↦ ?_⟩
      rw [czxFusion_contract, evalWord_idTensor_toMPSTensor]
      congr 3
      funext a
      exact pairDelta_eq a

/-! ### The two fusion trees of three generators -/

/-- The integer matrix of `1 ⊗ V̂`, the left boundary of the tree fusing the last
two generators first. The tree fusing the first two generators first is `V̂ ⊗ 1`, the
matrix `czxAssocLeftInt` of `eq:Uanomal`. This one is not the right end
`czxAssocRightInt = 1 ⊗ V` of `eq:Uanomal`: it carries `V̂` rather than `V`, as a row
rather than a column. -/
def czxRightTreeInt : Matrix (Fin 2) (Fin 8) ℤ :=
  !![0, 0, 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 1, 0]

private theorem kronId_complexOfInt {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℤ) (D : ℕ) :
    kronId (complexOfInt X) D = complexOfInt ((X ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℤ)).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm) :=
  kronId_complexOfRing (Int.castRingHom ℂ) X D

private theorem idKron_complexOfInt {m n : ℕ} (D : ℕ) (X : Matrix (Fin m) (Fin n) ℤ) :
    idKron D (complexOfInt X) = complexOfInt (((1 : Matrix (Fin D) (Fin D) ℤ) ⊗ₖ X).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm) :=
  idKron_complexOfRing (Int.castRingHom ℂ) D X

private theorem assocInv_two_two_two :
    mulTensorAssocInvMatrix 2 2 2 = (1 : Matrix (Fin 8) (Fin 8) ℂ) := by
  rw [mulTensorAssocInvMatrix_eq_finCongr]
  exact finCongr_toMatrix_eq_one _

private theorem assocInv_two_one_two :
    mulTensorAssocInvMatrix 2 1 2 = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [mulTensorAssocInvMatrix_eq_finCongr]
  exact finCongr_toMatrix_eq_one _

private theorem castMat_gen_gen_gen :
    czxFamily.castMat (mul_assoc czxGen czxGen czxGen).symm =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [GroupFamily.castMat_eq_finCongr]
  exact finCongr_toMatrix_eq_one _

private theorem castMat_gen_one_gen :
    czxFamily.castMat (mul_assoc czxGen 1 czxGen).symm = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [GroupFamily.castMat_eq_finCongr]
  exact finCongr_toMatrix_eq_one _

/-- The left fusion tree of `(s,s,s)`, which fuses the first two factors first, is the
integer matrix `czxAssocLeftInt`; it is one of the two trees compared in `eq:3-cocycle` of
arXiv:2502.20257. -/
theorem czxFusionData_leftV_gen_gen_gen :
    czxFusionData.leftV czxGen czxGen czxGen = complexOfInt czxAssocLeftInt := by
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) * kronId (complexOfInt czxFusionVHatInt) 2 = _
  rw [Matrix.one_mul, kronId_complexOfInt]
  congr 1
  decide

/-- The right fusion tree of `(s,s,s)`, which fuses the last two factors first, is the
integer matrix `czxRightTreeInt`; it is the other tree compared in `eq:3-cocycle` of
arXiv:2502.20257. -/
theorem czxFusionData_rightV_gen_gen_gen :
    czxFusionData.rightV czxGen czxGen czxGen = complexOfInt czxRightTreeInt := by
  rw [GroupFamily.FusionData.rightV, castMat_gen_gen_gen]
  change (1 : Matrix (Fin 2) (Fin 2) ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) *
      idKron 2 (complexOfInt czxFusionVHatInt) * mulTensorAssocInvMatrix 2 2 2) = _
  rw [assocInv_two_two_two, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, idKron_complexOfInt]
  congr 1
  decide

private theorem czx_left_pair_int : ∀ i j k l : Fin 2,
    czxAssocLeftInt * czxDecoratedCubeInt i j * czxDecoratedCubeInt k l =
      czxDecoratedIntTensor i j * czxAssocLeftInt * czxDecoratedCubeInt k l := by
  decide

private theorem czx_right_pair_int : ∀ i j k l : Fin 2,
    czxRightTreeInt * czxDecoratedCubeInt i j * czxDecoratedCubeInt k l =
      czxDecoratedIntTensor i j * czxRightTreeInt * czxDecoratedCubeInt k l := by
  decide

private theorem czx_letter_int : ∀ i j : Fin 2,
    czxAssocLeftInt * czxDecoratedCubeInt i j = -(czxRightTreeInt * czxDecoratedCubeInt i j) := by
  decide

private theorem czx_pair (L : Matrix (Fin 2) (Fin 8) ℤ)
    (hL : ∀ i j k l : Fin 2, L * czxDecoratedCubeInt i j * czxDecoratedCubeInt k l =
      czxDecoratedIntTensor i j * L * czxDecoratedCubeInt k l) (a b : Fin 4) :
    complexOfInt L * czxDecoratedCube.toMPSTensor a * czxDecoratedCube.toMPSTensor b =
      czxDecoratedTensor.toMPSTensor a * complexOfInt L * czxDecoratedCube.toMPSTensor b := by
  change complexOfInt L * czxDecoratedCube _ _ * czxDecoratedCube _ _ =
    czxDecoratedTensor _ _ * complexOfInt L * czxDecoratedCube _ _
  rw [czxDecoratedCube_eq, czxDecoratedCube_eq, czxDecoratedTensor, ← complexOfInt_mul,
    ← complexOfInt_mul, ← complexOfInt_mul, ← complexOfInt_mul, hL]

private theorem czx_letter (a : Fin 4) :
    complexOfInt czxAssocLeftInt * czxDecoratedCube.toMPSTensor a =
      (-1 : ℂ) • (complexOfInt czxRightTreeInt * czxDecoratedCube.toMPSTensor a) := by
  change complexOfInt czxAssocLeftInt * czxDecoratedCube _ _ =
    (-1 : ℂ) • (complexOfInt czxRightTreeInt * czxDecoratedCube _ _)
  rw [czxDecoratedCube_eq, ← complexOfInt_mul, ← complexOfInt_mul, czx_letter_int,
    complexOfInt_neg, neg_one_smul]

/-- **The associator of three generators is `-1`**: with the fusion tensors of
`czxFusionData`, the tree fusing the first two generators first equals `-1` times the
tree fusing the last two first, against every nonempty word.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 481--499
(`eq:Uanomal`) and 1128--1136 ("which has an anomaly, i.e., `ω = -1`"). -/
theorem czxFusionData_isAssociator_gen_gen_gen :
    czxFusionData.IsAssociator czxGen czxGen czxGen (-1) := by
  unfold GroupFamily.FusionData.IsAssociator
  rw [czxFusionData_leftV_gen_gen_gen, czxFusionData_rightV_gen_gen_gen]
  exact MPSTensor.IsDressedProportional.of_forall_mul_mul (czx_pair _ czx_left_pair_int)
    (czx_pair _ czx_right_pair_int) czx_letter

/-- `ω(g,g,g) = -1` for the fusion tensors of `czxFusionData`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 481--499 and
1128--1136. -/
theorem czxFusionData_omega_gen_gen_gen : czxFusionData.omega czxGen czxGen czxGen = -1 := by
  apply Units.ext
  rw [← GroupFamily.FusionData.eq_omega_of_isAssociator czxFamily_isNormalRepresentation
    czxFusionData_isAssociator_gen_gen_gen]
  simp

/-- `ω(g,1,g) = 1` for the fusion tensors of `czxFusionData`, which are trivial
whenever a factor is the identity: both fusion trees are `V̂`. -/
theorem czxFusionData_omega_gen_one_gen : czxFusionData.omega czxGen 1 czxGen = 1 := by
  have hL : czxFusionData.leftV czxGen 1 czxGen = czxFusionVHat := by
    change czxFusionVHat * kronId (1 : Matrix (Fin 2) (Fin 2) ℂ) 2 = czxFusionVHat
    rw [kronId_one, Matrix.mul_one]
  have hR : czxFusionData.rightV czxGen 1 czxGen = czxFusionVHat := by
    rw [GroupFamily.FusionData.rightV, castMat_gen_one_gen]
    change (1 : Matrix (Fin 1) (Fin 1) ℂ) * (czxFusionVHat *
        idKron 2 (1 : Matrix (Fin 2) (Fin 2) ℂ) * mulTensorAssocInvMatrix 2 1 2) = czxFusionVHat
    rw [idKron_one, Matrix.mul_one, assocInv_two_one_two, Matrix.mul_one, Matrix.one_mul]
  have h : czxFusionData.IsAssociator czxGen 1 czxGen 1 := by
    unfold GroupFamily.FusionData.IsAssociator
    rw [hR, ← hL]
    exact MPSTensor.IsDressedProportional.refl _ _
  apply Units.ext
  rw [← GroupFamily.FusionData.eq_omega_of_isAssociator czxFamily_isNormalRepresentation h]
  simp

/-! ### The anomaly class -/

/-- The gauge-invariant product `ω(g,1,g) ω(g,g,g)` of the fusion tensors of
`czxFusionData` is `-1`. -/
theorem cyclicInvariant_czxFusionData :
    ScalarThreeCochain.cyclicInvariant czxFusionData.omega czxGen 2 = -1 := by
  simp only [ScalarThreeCochain.cyclicInvariant, Finset.prod_range_succ, Finset.prod_range_zero,
    one_mul, pow_zero, pow_one, czxFusionData_omega_gen_one_gen, czxFusionData_omega_gen_gen_gen]

/-- **For every choice of fusion tensors of the decorated CZX representation**, the
gauge-invariant product `ω(g,1,g) ω(g,g,g)` is `-1`.

Source: arXiv:2502.20257, `eq:omegagauge`; arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 1128--1136. -/
theorem cyclicInvariant_omega_czx (fd : czxFamily.FusionData) :
    ScalarThreeCochain.cyclicInvariant fd.omega czxGen 2 = -1 := by
  rw [(GroupFamily.FusionData.omega_cohomologousTo czxFamily_isNormalRepresentation
    czxFusionData fd).cyclicInvariant_eq czxGen_pow_two, cyclicInvariant_czxFusionData]

/-- **The decorated CZX representation is anomalous**: for every choice of fusion
tensors, the anomaly three-cocycle is not cohomologous to the trivial one.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 1128--1136 ("the CZX
symmetry ..., which has an anomaly, i.e., `ω = -1`"); arXiv:2502.20257,
`eq:omegagauge` and the sentence following it. -/
theorem not_isTrivialGaugeClass_omega_czx (fd : czxFamily.FusionData) :
    ¬ ScalarThreeCochain.IsTrivialGaugeClass fd.omega := by
  refine ScalarThreeCochain.not_isTrivialGaugeClass_of_cyclicInvariant_ne_one czxGen_pow_two ?_
  rw [cyclicInvariant_omega_czx]
  intro h
  have := congrArg Units.val h
  norm_num at this

end CZXCompression
