/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.PhysicalRotation
import QICLean.Kraus.Transfer
import QICLean.Kraus.MixedMap
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Physical matrices of matrix product tensors

Reshape a tensor from its physical-indexed family of bond matrices into a map from the
virtual pair space to the physical space. Reshaping is invertible, commutes with physical
index rotation, and identifies the physical Gram matrix with entries of the mixed transfer
map. These finite-dimensional identities do not require polar decomposition, canonical
gauges, spectral convergence, or circuit synthesis.

The declarations retain their original names. `Preparation.BlockedPolar` builds polar
factors on this interface; `Preparation.ApproximatingState` adds convergence statements.

## Main declarations

* `MPSTensor.physicalMatrix`, `MPSTensor.ofPhysicalMatrix`: inverse tensor reshapes.
* `MPSTensor.physicalMatrix_rotatePhysical`: compatibility with physical-index rotation.
* `MPSTensor.conjTranspose_physicalMatrix_mul_physicalMatrix_apply`: mixed Gram entries.
* `MPSTensor.conjTranspose_physicalMatrix_mul_apply`: Gram entries from the transfer map.

## References

* arXiv:2307.01696, paragraph "Approximation through the fixed-point state" and eq. (8).
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {n m D : ℕ}

/-- The tensor `B` read as the matrix of the linear map `ℂ^{D²} → ℂ^n`, `(i, (α, β)) ↦ B^i_{αβ}`.

arXiv:2307.01696, paragraph "Approximation through the fixed-point state": the blocked tensor
is interpreted "as a map from the `D²`-dimensional virtual space to the `d^q`-dimensional
physical space". -/
def physicalMatrix (A : MPSTensor n D) : Matrix (Fin n) (Fin D × Fin D) ℂ :=
  fun i p => A i p.1 p.2

/-- The tensor whose physical matrix is `R`. -/
def ofPhysicalMatrix (R : Matrix (Fin n) (Fin D × Fin D) ℂ) : MPSTensor n D :=
  fun i α β => R i (α, β)

/-- Reading the physical matrix of a tensor back as a tensor returns the tensor. -/
@[simp] lemma ofPhysicalMatrix_physicalMatrix (A : MPSTensor n D) :
    ofPhysicalMatrix (physicalMatrix A) = A := rfl

/-- The physical matrix of the tensor built from a matrix `R` is `R`. -/
@[simp] lemma physicalMatrix_ofPhysicalMatrix (R : Matrix (Fin n) (Fin D × Fin D) ℂ) :
    physicalMatrix (ofPhysicalMatrix R) = R := rfl

/-- A tensor is determined by its physical matrix. -/
lemma physicalMatrix_injective : Function.Injective (physicalMatrix (n := n) (D := D)) :=
  fun A B h => by rw [← ofPhysicalMatrix_physicalMatrix A, h, ofPhysicalMatrix_physicalMatrix]

/-- The physical matrix of `W · A` is `W` times the physical matrix of `A`. -/
lemma physicalMatrix_rotatePhysical (W : Matrix (Fin m) (Fin n) ℂ) (A : MPSTensor n D) :
    physicalMatrix (rotatePhysical W A) = W * physicalMatrix A := by
  ext i p
  simp [physicalMatrix, rotatePhysical, Matrix.mul_apply, Matrix.sum_apply]

/-- The mixed Gram matrix `Xᴴ Y` of the physical matrices of two tensors is a rearrangement of
their mixed transfer map: `(Xᴴ Y)_{(α,β),(α',β')} = E_{YX}(|β'⟩⟨β|)_{α' α}`. -/
theorem conjTranspose_physicalMatrix_mul_physicalMatrix_apply {n D₁ D₂ : ℕ}
    (X : MPSTensor n D₁) (Y : MPSTensor n D₂) (a : Fin D₁ × Fin D₁) (b : Fin D₂ × Fin D₂) :
    ((physicalMatrix X)ᴴ * physicalMatrix Y) a b =
      Kraus.mixedMapLM Y X (Matrix.single b.2 a.2 1) b.1 a.1 := by
  rw [Kraus.mixedMapLM_apply, Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single a.2]
  · simp [physicalMatrix, Matrix.mul_apply, Matrix.single_apply, mul_comm]
  · intro y _ hy
    simp [Matrix.mul_apply, Ne.symm hy]
  · simp

/-- The Gram matrix `Bᴴ B` of the physical matrix of a tensor is a rearrangement of its transfer
map: `(Bᴴ B)_{(α,β),(α',β')} = E_B(|β'⟩⟨β|)_{α' α}`.

arXiv:2307.01696, eq. (8): `E_B` is `P† P = B† B` with legs regrouped. -/
theorem conjTranspose_physicalMatrix_mul_apply (B : MPSTensor n D) (a b : Fin D × Fin D) :
    ((physicalMatrix B)ᴴ * physicalMatrix B) a b =
      Kraus.transferMap B (Matrix.single b.2 a.2 1) b.1 a.1 := by
  rw [conjTranspose_physicalMatrix_mul_physicalMatrix_apply, Kraus.mixedMapLM_self]

/-- Conjugation of the bond matrices acts on the virtual pair index by
`Xᵀ ⊗ Y`. Source: arXiv:1010.3732, Section II.C, virtual gauge action. -/
theorem physicalMatrix_mul_left_right {d D : ℕ} (A : MPSTensor d D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physicalMatrix (fun i => X * A i * Y) = physicalMatrix A * (Xᵀ ⊗ₖ Y) := by
  ext i ⟨a, b⟩
  simp only [physicalMatrix, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

/-- The physical contraction of two tensor reshapes is the trace pairing of
individual bond matrices. -/
theorem physicalMatrix_mul_conjTranspose_apply
    (A B : MPSTensor n D) (i j : Fin n) :
    (physicalMatrix A * (physicalMatrix B)ᴴ) i j =
      Matrix.trace (A i * (B j)ᴴ) := by
  simp only [Matrix.mul_apply, physicalMatrix, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag]

end MPSTensor
