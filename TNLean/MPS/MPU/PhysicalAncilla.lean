/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Basic

/-!
# Attaching a physical identity ancilla to a matrix product unitary

This file formalizes the local tensor operation
$\mathcal U^{(x)} = \mathcal U \otimes I_x$ from arXiv:1703.09188,
lines 706--724.  It enlarges only the physical alphabet, from \(d\) to \(d x\);
the virtual bond dimension remains \(D\).

## Main definitions

* `MPOTensor.tensorPhysicalId`: attach an identity ancilla at each physical site.
* `MPOTensor.physicalAncillaConfigEquiv`: split every enlarged physical configuration
  into its original and ancilla configurations.

## Main results

* `MPOTensor.mpo_tensorPhysicalId`: the generated MPO is the reindexed Kronecker
  product of the original MPO and the ancilla identity.
* `MPOTensor.IsMPU.tensorPhysicalId`: identity-ancilla attachment preserves the MPU
  property.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D x : ℕ}

/-- Attach a physical identity ancilla of dimension \(x\) to an MPO tensor, without
changing its virtual bond dimension \(D\).

In coordinates, the enlarged physical indices are pairs `(i, a)` and `(j, b)`, and
$\mathcal U^{(x)}_{(i,a),(j,b);\beta,\alpha}
  = \mathcal U_{i,j;\beta,\alpha}\,\delta_{a,b}$.

Source: arXiv:1703.09188, lines 706--724. -/
def tensorPhysicalId (U : MPOTensor d D) (x : ℕ) : MPOTensor (d * x) D :=
  fun ia jb ↦ if ia.modNat = jb.modNat then U ia.divNat jb.divNat else 0

/-- Coordinate formula for physical identity-ancilla attachment. -/
@[simp] theorem tensorPhysicalId_apply (U : MPOTensor d D) (i j : Fin d)
    (a b : Fin x) (β α : Fin D) :
    tensorPhysicalId U x (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) β α =
      U i j β α * if a = b then 1 else 0 := by
  by_cases h : a = b <;> simp [tensorPhysicalId, h]

/-- Each fixed-virtual physical slice is the Kronecker product with the ancilla
identity, reindexed from pairs to the standard `Fin (d * x)` product encoding. -/
theorem physicalSlice_tensorPhysicalId (U : MPOTensor d D) (x : ℕ) (β α : Fin D) :
    physicalSlice (tensorPhysicalId U x) β α =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (physicalSlice U β α ⊗ₖ (1 : Matrix (Fin x) (Fin x) ℂ)) := by
  ext ia jb
  by_cases h : ia.modNat = jb.modNat <;>
    simp [physicalSlice, tensorPhysicalId, Matrix.reindex_apply, h]

/-- Split a sitewise enlarged physical configuration into its original and
ancilla configurations. -/
def physicalAncillaConfigEquiv (N d x : ℕ) :
    (Fin N → Fin (d * x)) ≃ (Fin N → Fin d) × (Fin N → Fin x) :=
  (Equiv.arrowCongr (Equiv.refl (Fin N)) finProdFinEquiv.symm).trans
    (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ ↦ Fin d) (fun _ ↦ Fin x))

private theorem evalWord_tensorPhysicalId (U : MPOTensor d D) (x : ℕ)
    (is js : List (Fin (d * x))) :
    evalWord (tensorPhysicalId U x) is js =
      if is.length = js.length ∧ is.map Fin.modNat = js.map Fin.modNat then
        evalWord U (is.map Fin.divNat) (js.map Fin.divNat)
      else 0 := by
  induction is generalizing js with
  | nil => cases js <;> simp [evalWord]
  | cons i is ih =>
      cases js with
      | nil => simp [evalWord]
      | cons j js =>
          by_cases h : i.modNat = j.modNat
          · simp [evalWord, tensorPhysicalId, h, ih]
          · simp [evalWord, tensorPhysicalId, h]

/-- The closed MPO generated after identity-ancilla attachment is the Kronecker
product of the original closed MPO and the ancilla identity, in the canonical
sitewise product coordinates.

Source: arXiv:1703.09188, lines 706--724. -/
theorem mpo_tensorPhysicalId (U : MPOTensor d D) (x N : ℕ) :
    mpo (tensorPhysicalId U x) N =
      Matrix.reindex (physicalAncillaConfigEquiv N d x).symm
        (physicalAncillaConfigEquiv N d x).symm
        (mpo U N ⊗ₖ (1 : Matrix (Fin N → Fin x) (Fin N → Fin x) ℂ)) := by
  ext σ τ
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mpo_apply, mpoMatrixEntry]
  rw [evalWord_tensorPhysicalId]
  simp only [List.length_ofFn, true_and, List.map_ofFn]
  by_cases h : (fun c ↦ (σ c).modNat) = (fun c ↦ (τ c).modNat) <;>
    simp [physicalAncillaConfigEquiv, Equiv.arrowCongr, Function.comp_def, h]

/-- Attaching a nonempty physical identity ancilla preserves the matrix product
unitary property.

Source: arXiv:1703.09188, lines 706--724. -/
theorem IsMPU.tensorPhysicalId {U : MPOTensor d D} (hU : IsMPU U)
    (x : ℕ) (_hx : 0 < x) : IsMPU (tensorPhysicalId U x) := by
  intro N hN
  rw [mpo_tensorPhysicalId]
  apply Matrix.reindex_mem_unitaryGroup
  rw [Matrix.mem_unitaryGroup_iff]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul, hU.mpo_mul_conjTranspose_mpo hN,
    Matrix.one_mul, Matrix.one_kronecker_one]

end MPOTensor
