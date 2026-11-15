/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.PhysicalAncilla
import TNLean.MPS.MPU.KetLeftMul

/-!
# Physical output actions with an identity ancilla

The physical matrix \(Q\otimes I_x\), in the product coordinates of
`tensorPhysicalId`, acts on every enlarged physical operator. Its output
action on an ancilla-attached tensor is the ancilla attachment of the
original output action.

Source: arXiv:1703.09188, identity ancillas at lines 706--724 and the output
transformation in Section `othersymmetries`, lines 1301--1322.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D : ℕ}

/-- The full physical matrix \(Q\otimes I_x\), in sitewise product coordinates.
Source: arXiv:1703.09188, identity ancillas, lines 706--724. -/
noncomputable def physicalIdMatrix (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    Matrix (Fin (d * x)) (Fin (d * x)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Q ⊗ₖ (1 : Matrix (Fin x) (Fin x) ℂ))

/-- In product coordinates the ancillary physical matrix fixes the ancilla. -/
@[simp] theorem physicalIdMatrix_apply (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ)
    (i j : Fin d) (a b : Fin x) :
    physicalIdMatrix Q x (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      Q i j * if a = b then 1 else 0 := by
  simp [physicalIdMatrix, Matrix.reindex_apply, Matrix.one_apply]

/-- Identity-ancilla extension preserves the identity physical matrix. -/
@[simp] theorem physicalIdMatrix_one (d x : ℕ) :
    physicalIdMatrix (1 : Matrix (Fin d) (Fin d) ℂ) x = 1 := by
  simp [physicalIdMatrix, Matrix.one_kronecker_one]

/-- Identity-ancilla extension preserves physical matrix multiplication. -/
theorem physicalIdMatrix_mul (P Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    physicalIdMatrix P x * physicalIdMatrix Q x = physicalIdMatrix (P * Q) x := by
  unfold physicalIdMatrix
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ finProdFinEquiv finProdFinEquiv
    finProdFinEquiv]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Identity-ancilla extension commutes with adjunction. -/
theorem physicalIdMatrix_conjTranspose (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    (physicalIdMatrix Q x)ᴴ = physicalIdMatrix Qᴴ x := by
  simp [physicalIdMatrix, Matrix.conjTranspose_reindex, Matrix.conjTranspose_kronecker]

/-- Identity-ancilla extension commutes with transposition. -/
theorem physicalIdMatrix_transpose (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    (physicalIdMatrix Q x)ᵀ = physicalIdMatrix Qᵀ x := by
  ext i j
  simp [physicalIdMatrix, Matrix.transpose_apply, Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, eq_comm]

/-- A real physical matrix remains real after adjoining an identity ancilla. -/
theorem physicalIdMatrix_map_star (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ)
    (hQ : Q.map (starRingEnd ℂ) = Q) :
    (physicalIdMatrix Q x).map (starRingEnd ℂ) = physicalIdMatrix Q x := by
  ext i j
  have h := congrFun (congrFun hQ i.divNat) j.divNat
  by_cases hab : i.modNat = j.modNat
  · simpa [physicalIdMatrix, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, hab] using h
  · simp [physicalIdMatrix, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, hab]

/-- A physical unitary tensored with an identity ancilla is unitary. -/
theorem physicalIdMatrix_mem_unitaryGroup (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    physicalIdMatrix Q x ∈ Matrix.unitaryGroup (Fin (d * x)) ℂ :=
  Matrix.reindex_mem_unitaryGroup _ _ (Matrix.kronecker_mem_unitary hQ (one_mem _))

/-- Acting by \(Q\otimes I_x\) after identity-ancilla attachment is the
identity-ancilla attachment of the original physical output action.
Source: arXiv:1703.09188, lines 706--724 and Lemma `lemma:sym-trafo-swap`. -/
theorem ketLeftMul_tensorPhysicalId (U : MPOTensor d D)
    (Q : Matrix (Fin d) (Fin d) ℂ) (x : ℕ) :
    (tensorPhysicalId U x).ketLeftMul (physicalIdMatrix Q x) =
      tensorPhysicalId (U.ketLeftMul Q) x := by
  classical
  funext i j
  simp only [ketLeftMul]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  by_cases hab : i.modNat = j.modNat
  · simp [physicalIdMatrix, tensorPhysicalId, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, hab]
  · simp [physicalIdMatrix, tensorPhysicalId, Matrix.reindex_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, hab]

end MPOTensor
