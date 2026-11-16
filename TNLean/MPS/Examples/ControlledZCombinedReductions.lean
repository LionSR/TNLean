/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.ReductionCertificates
import TNLean.MPS.Examples.ControlledZCombinedSymmetry

/-!
# Explicit reductions for the combined controlled-Z symmetry

The action reductions for the two invariant states of arXiv:2502.20257, line 3970, and the
fusion reductions for their common symmetry are given by finite rational matrices.
Their local compression identities imply the reduction equations on every word.
These choices specify the data needed to compare the two action L-symbols.
-/

noncomputable section

open scoped Matrix Kronecker BigOperators
open MPOTensor MPOTensor.GroupFamily MPSTensor TNLean.Algebra

namespace ControlledZGauging

/-- The rational matrices of the combined family, indexed by its two bits. -/
def combinedLabelRational : (p q : Fin 2) → Fin 2 → Fin 2 →
    Matrix (Fin (czBondDim q)) (Fin (czBondDim q)) ℚ
  | p, 0, i, j => Matrix.of fun _ _ ↦ if i = j then (-1) ^ (p.val * j.val) else 0
  | p, 1, i, j => Matrix.of fun l r ↦
      if i = j ∧ r.val = j.val then (-1) ^ (p.val * j.val + l.val * j.val) else 0

/-- The rational coefficient tensor for a group element of the combined symmetry. -/
def combinedRationalTensor (g : Multiplicative (ZMod 2 × ZMod 2)) :=
  combinedLabelRational g.toAdd.1 g.toAdd.2

/-- The rational form of the existing bond-three state. -/
def stateRational (i : Fin 2) : Matrix (Fin 3) (Fin 3) ℚ :=
  (stateInt i).map (Int.castRingHom ℚ)

/-- The rational form of the existing zero product state. -/
def zeroRational (i : Fin 2) : Matrix (Fin 1) (Fin 1) ℚ :=
  Matrix.of fun _ _ ↦ if i = 0 then 1 else 0

/-- Rational action of a combined tensor on a rational state, with the actual row-major
bond order used by the MPO action. -/
def combinedRationalAction {D : ℕ} (g : Multiplicative (ZMod 2 × ZMod 2))
    (A : Fin 2 → Matrix (Fin D) (Fin D) ℚ) (i : Fin 2) :=
  (∑ j, combinedRationalTensor g i j ⊗ₖ A j).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- The rational stacked product of two actual combined tensors. -/
def combinedRationalProduct (g h : Multiplicative (ZMod 2 × ZMod 2)) (i j : Fin 2) :=
  (∑ k, combinedRationalTensor g i k ⊗ₖ combinedRationalTensor h k j).submatrix
    finProdFinEquiv.symm finProdFinEquiv.symm

/-- Left action reductions for the bond-three state. -/
def combinedStateV : (p q : Fin 2) → Matrix (Fin 3) (Fin (czBondDim q * 3)) ℚ
  | 0, 0 => (1 : Matrix (Fin 3) (Fin 3) ℚ)
  | 1, 0 => !![1, 0, 0; 0, -1, 0; 0, 0, -1]
  | 0, 1 => !![0, 2, 2, 0, 0, 0; 1, 0, 0, -1, 0, 0; 1, 0, 0, 1, 0, 0]
  | 1, 1 => !![0, -2, -2, 0, 0, 0; 1, 0, 0, -1, 0, 0; 1, 0, 0, 1, 0, 0]

/-- Right action reductions for the bond-three state. -/
def combinedStateW : (p q : Fin 2) → Matrix (Fin (czBondDim q * 3)) (Fin 3) ℚ
  | 0, 0 => (1 : Matrix (Fin 3) (Fin 3) ℚ)
  | 1, 0 => !![1, 0, 0; 0, -1, 0; 0, 0, -1]
  | 0, 1 => !![0, 1/2, 1/2; 1/2, 0, 0; 0, 0, 0; 0, -1/2, 1/2; -1/2, 0, 0; 0, 0, 0]
  | 1, 1 => !![0, 1/2, 1/2; -1/2, 0, 0; 0, 0, 0; 0, -1/2, 1/2; 1/2, 0, 0; 0, 0, 0]

/-- Left action reductions for the reference product state. -/
def combinedZeroV : (q : Fin 2) → Matrix (Fin 1) (Fin (czBondDim q * 1)) ℚ
  | 0 => (1 : Matrix (Fin 1) (Fin 1) ℚ)
  | 1 => !![1, 0]

/-- Right action reductions for the reference product state. -/
def combinedZeroW : (q : Fin 2) → Matrix (Fin (czBondDim q * 1)) (Fin 1) ℚ
  | 0 => (1 : Matrix (Fin 1) (Fin 1) ℚ)
  | 1 => !![1; 1]

/-- Left fusion reductions; two controlled-Z factors reduce onto their identity tensor. -/
def combinedFusionV : (q r : Fin 2) →
    Matrix (Fin (czBondDim (q + r))) (Fin (czBondDim q * czBondDim r)) ℚ
  | 0, 0 => (1 : Matrix (Fin 1) (Fin 1) ℚ)
  | 0, 1 => (1 : Matrix (Fin 2) (Fin 2) ℚ)
  | 1, 0 => (1 : Matrix (Fin 2) (Fin 2) ℚ)
  | 1, 1 => !![1, 0, 0, 0]

/-- Right fusion reductions, in the same row-major bond order. -/
def combinedFusionW : (q r : Fin 2) →
    Matrix (Fin (czBondDim q * czBondDim r)) (Fin (czBondDim (q + r))) ℚ
  | 0, 0 => (1 : Matrix (Fin 1) (Fin 1) ℚ)
  | 0, 1 => (1 : Matrix (Fin 2) (Fin 2) ℚ)
  | 1, 0 => (1 : Matrix (Fin 2) (Fin 2) ℚ)
  | 1, 1 => !![1; 1; 1; 1]

/-- The rational tensor is exactly the previously constructed complex MPO tensor. -/
theorem complexOfRing_combinedRationalTensor (g : Multiplicative (ZMod 2 × ZMod 2))
    (i j : Fin 2) :
    complexOfRing (Rat.castHom ℂ) (combinedRationalTensor g i j) =
      combinedFamily.tensor g i j := by
  -- The pinned ZMod 2 is semireducibly Fin 2. This coefficient proof needs backward
  -- elaboration to unfold that identification throughout its dependent matrix indices.
  set_option backward.isDefEq.respectTransparency false in
    ext l r
    change (Rat.castHom ℂ) (combinedLabelRational g.toAdd.1 g.toAdd.2 i j l r) =
      (combinedZCharacter g j : ℂ) * czRepTensor g.toAdd.2 i j l r
    revert g
    refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;>
      dsimp only [toAdd_ofAdd] <;> intro l r <;>
      fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases r <;>
      norm_num [combinedLabelRational, combinedZCharacter, czRepTensor,
        czMPUTensor, czSign, idTensor, Matrix.one_apply, ZMod.val, czBondDim]

/-- The rational state letters map to the original complex bond-three state. -/
theorem complexOfRing_stateRational (i : Fin 2) :
    complexOfRing (Rat.castHom ℂ) (stateRational i) = stateTensor i := by
  ext l r
  simp [complexOfRing, stateRational, stateTensor]

/-- The rational product-state letters map to the complex zero product state. -/
theorem complexOfRing_zeroRational (i : Fin 2) :
    complexOfRing (Rat.castHom ℂ) (zeroRational i) = zeroState i := by
  ext l r
  by_cases hi : i = 0 <;> simp [complexOfRing, zeroRational, zeroState, hi]

/-- The rational action contraction maps to the actual complex MPO action tensor. -/
theorem complexOfRing_combinedRationalAction {D : ℕ}
    (g : Multiplicative (ZMod 2 × ZMod 2))
    (A : Fin 2 → Matrix (Fin D) (Fin D) ℚ) (i : Fin 2) :
    complexOfRing (Rat.castHom ℂ) (combinedRationalAction g A i) =
      actTensor (combinedFamily.tensor g) (fun j ↦ complexOfRing (Rat.castHom ℂ) (A j)) i := by
  simp only [combinedRationalAction, actTensor_apply, complexOfRing_submatrix,
    complexOfRing_sum, complexOfRing_kronecker, complexOfRing_combinedRationalTensor]
  rfl

/-- The rational stacked product maps to the actual product of the complex MPO tensors. -/
theorem complexOfRing_combinedRationalProduct
    (g h : Multiplicative (ZMod 2 × ZMod 2)) (i j : Fin 2) :
    complexOfRing (Rat.castHom ℂ) (combinedRationalProduct g h i j) =
      mulTensor (combinedFamily.tensor g) (combinedFamily.tensor h) i j := by
  simp only [combinedRationalProduct, mulTensor_apply, complexOfRing_submatrix,
    complexOfRing_sum, complexOfRing_kronecker, complexOfRing_combinedRationalTensor]
  rfl

private theorem combinedState_local : ∀ g : Multiplicative (ZMod 2 × ZMod 2),
    let V := combinedStateV g.toAdd.1 g.toAdd.2
    let W := combinedStateW g.toAdd.1 g.toAdd.2
    let B := combinedRationalAction g stateRational
    V * W = 1 ∧ (∀ i, V * B i * W = stateRational i) ∧
      ∀ i j, B i * W * V * B j = B i * B j := by
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;> decide +kernel

private theorem combinedZero_local : ∀ g : Multiplicative (ZMod 2 × ZMod 2),
    let V := combinedZeroV g.toAdd.2
    let W := combinedZeroW g.toAdd.2
    let B := combinedRationalAction g zeroRational
    V * W = 1 ∧ (∀ i, V * B i * W = zeroRational i) ∧
      ∀ i j, B i * W * V * B j = B i * B j := by
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;> decide +kernel

private theorem combinedFusion_local : ∀ g h : Multiplicative (ZMod 2 × ZMod 2),
    let V := combinedFusionV g.toAdd.2 h.toAdd.2
    let W := combinedFusionW g.toAdd.2 h.toAdd.2
    let B := fun a : Fin (2 * 2) ↦ combinedRationalProduct g h a.divNat a.modNat
    let A := fun a : Fin (2 * 2) ↦ combinedRationalTensor (g * h) a.divNat a.modNat
    V * W = 1 ∧ (∀ i, V * B i * W = A i) ∧
      ∀ i j, B i * W * V * B j = B i * B j := by
  refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_
  all_goals refine Multiplicative.forall_zmod_two_prod ?_ ?_ ?_ ?_ <;> decide +kernel

/-- Explicit action reductions onto the normal bond-three controlled-Z state. -/
def combinedStateActionData : ActionData combinedFamily stateTensor where
  V g := complexOfRing (Rat.castHom ℂ) (combinedStateV g.toAdd.1 g.toAdd.2)
  W g := complexOfRing (Rat.castHom ℂ) (combinedStateW g.toAdd.1 g.toAdd.2)
  isReduction g := by
    have hc := combinedState_local g
    have hr := isReduction_complexOfRing_of_local_compression (Rat.castHom ℂ)
      (combinedRationalAction g stateRational) stateRational _ _ hc.1 hc.2.1 hc.2.2
    simp only [complexOfRing_combinedRationalAction, complexOfRing_stateRational] at hr
    convert hr using 1
    rfl

/-- Explicit action reductions onto the reference zero product state. -/
def combinedZeroActionData : ActionData combinedFamily zeroState where
  V g := complexOfRing (Rat.castHom ℂ) (combinedZeroV g.toAdd.2)
  W g := complexOfRing (Rat.castHom ℂ) (combinedZeroW g.toAdd.2)
  isReduction g := by
    have hc := combinedZero_local g
    have hr := isReduction_complexOfRing_of_local_compression (Rat.castHom ℂ)
      (combinedRationalAction g zeroRational) zeroRational _ _ hc.1 hc.2.1 hc.2.2
    simp only [complexOfRing_combinedRationalAction, complexOfRing_zeroRational] at hr
    convert hr using 1
    rfl

/-- Explicit fusion reductions for the same combined family used by both invariant states. -/
def combinedFusionData : FusionData combinedFamily where
  V g h := complexOfRing (Rat.castHom ℂ) (combinedFusionV g.toAdd.2 h.toAdd.2)
  W g h := complexOfRing (Rat.castHom ℂ) (combinedFusionW g.toAdd.2 h.toAdd.2)
  isReduction g h := by
    have hc := combinedFusion_local g h
    have hr := isReduction_complexOfRing_of_local_compression (Rat.castHom ℂ)
      (fun a : Fin (2 * 2) ↦ combinedRationalProduct g h a.divNat a.modNat)
      (fun a : Fin (2 * 2) ↦ combinedRationalTensor (g * h) a.divNat a.modNat)
      _ _ hc.1 hc.2.1 hc.2.2
    simp only [complexOfRing_combinedRationalProduct,
      complexOfRing_combinedRationalTensor] at hr
    convert hr using 1
    rfl

end ControlledZGauging
