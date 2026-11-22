/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Equivalence.Equivalence
import TNLean.MPS.MPU.CanonicalForm.PhysicalAncillaLeftMul

/-!
# Symmetries retaining a local physical matrix

The local matrix \(Q\) is retained as physical data. Adjoining an identity
ancilla replaces it by \(Q\otimes I_x\), rather than selecting a new
matrix from the enlarged dimension alone. The two sandwich actions are
defined on every enlarged operator, and compatibility with the
identity-ancilla embedding is derived from matrix multiplication.

This construction yields a finite-chain action at each specified physical
space. It does not assert that the sandwich actions form a globally
dimension-indexed coherent family. No general equivalence definition is
changed.

Source: arXiv:1703.09188, `SSymmetries`, lines 1301--1322, and
`def:equivalent-symmetry`, lines 1356--1366. The concrete source case is
\(Q=\mathbb S\), with the original physical factors distinguished.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

variable {d : ℕ}

private theorem operatorId_mul {N : ℕ}
    (X Y : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (x : ℕ) :
    tensorPhysicalIdOperator (X * Y) x =
      tensorPhysicalIdOperator X x * tensorPhysicalIdOperator Y x := by
  symm
  unfold tensorPhysicalIdOperator
  calc
    _ = Matrix.reindex (finTupleProdEquiv N d x).symm (finTupleProdEquiv N d x).symm
        ((X ⊗ₖ (1 : Matrix (Fin N → Fin x) (Fin N → Fin x) ℂ)) * (Y ⊗ₖ 1)) :=
      Matrix.reindexLinearEquiv_mul ℂ ℂ (finTupleProdEquiv N d x).symm
        (finTupleProdEquiv N d x).symm (finTupleProdEquiv N d x).symm _ _
    _ = _ := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

private theorem operatorId_conjTranspose {N : ℕ}
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (x : ℕ) :
    tensorPhysicalIdOperator Xᴴ x = (tensorPhysicalIdOperator X x)ᴴ := by
  simp [tensorPhysicalIdOperator, Matrix.conjTranspose_kronecker]

private theorem operatorId_transpose {N : ℕ}
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (x : ℕ) :
    tensorPhysicalIdOperator Xᵀ x = (tensorPhysicalIdOperator X x)ᵀ := by
  ext σ τ
  simp [tensorPhysicalIdOperator, Matrix.transpose_apply, Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, eq_comm]

private theorem operatorId_map_star {N : ℕ}
    (X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (x : ℕ) :
    tensorPhysicalIdOperator (X.map (starRingEnd ℂ)) x =
      (tensorPhysicalIdOperator X x).map (starRingEnd ℂ) := by
  ext σ τ
  by_cases h : (fun n ↦ (σ n).modNat) = (fun n ↦ (τ n).modNat)
  <;> simp [tensorPhysicalIdOperator, Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, h]

private theorem operatorId_tensorPower
    (Q : Matrix (Fin d) (Fin d) ℂ) (x N : ℕ) :
    tensorPhysicalIdOperator (Matrix.tensorPower N Q) x =
      Matrix.tensorPower N (physicalIdMatrix Q x) := by
  classical
  ext σ τ
  change (∏ n, Q (σ n).divNat (τ n).divNat) *
      (if (fun n => (σ n).modNat) = (fun n => (τ n).modNat) then 1 else 0) =
    ∏ n, Q (σ n).divNat (τ n).divNat *
      if (σ n).modNat = (τ n).modNat then 1 else 0
  rw [Finset.prod_mul_distrib, Fintype.prod_boole]
  by_cases h : ∀ n, (σ n).modNat = (τ n).modNat
  <;> simp [funext_iff, h]

namespace FiniteChainOperatorSymmetry

/-- The full action \(X\mapsto Q_NX^\dagger Q_N\), where \(Q_N=Q^{\otimes N}\).
The local matrix is explicit physical data. In the source symmetry class it
is a real symmetric unitary involution.
Source: arXiv:1703.09188, equation `SSymmetries-dagger`, lines 1305--1311. -/
noncomputable def daggerWithPhysicalMatrix (Q : Matrix (Fin d) (Fin d) ℂ) :
    FiniteChainOperatorSymmetry d where
  applicable := {N | 0 < N}
  action := fun {N} X ↦ Matrix.tensorPower N Q * Xᴴ * Matrix.tensorPower N Q

/-- The full action \(X\mapsto Q_NX^{\mathsf T}Q_N\), retaining its local
physical matrix. Source: arXiv:1703.09188, equation `SSymmetries-transpose`,
lines 1305--1311. -/
noncomputable def transposeWithPhysicalMatrix (Q : Matrix (Fin d) (Fin d) ℂ) :
    FiniteChainOperatorSymmetry d where
  applicable := {N | 0 < N}
  action := fun {N} X ↦ Matrix.tensorPower N Q * Xᵀ * Matrix.tensorPower N Q

/-- The full adjunction action with \(Q\otimes I_x\) is compatible with
adjoining the identity ancilla to every original operator.
Source: arXiv:1703.09188, `SSymmetries-dagger` and `def:equivalent-symmetry`. -/
theorem daggerWithPhysicalMatrix_tensorPhysicalId_semiconj
    (Q : Matrix (Fin d) (Fin d) ℂ) (x N : ℕ) :
    Function.Semiconj
      (fun X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ => tensorPhysicalIdOperator X x)
      (fun X => (daggerWithPhysicalMatrix Q).action X)
      (fun X => (daggerWithPhysicalMatrix (physicalIdMatrix Q x)).action X) := by
  intro X
  change tensorPhysicalIdOperator
      (Matrix.tensorPower N Q * Xᴴ * Matrix.tensorPower N Q) x = _
  simp only [daggerWithPhysicalMatrix, operatorId_mul, operatorId_conjTranspose,
    operatorId_tensorPower]

/-- The full transposition action with \(Q\otimes I_x\) is compatible with
adjoining the identity ancilla to every original operator.
Source: arXiv:1703.09188, `SSymmetries-transpose` and `def:equivalent-symmetry`. -/
theorem transposeWithPhysicalMatrix_tensorPhysicalId_semiconj
    (Q : Matrix (Fin d) (Fin d) ℂ) (x N : ℕ) :
    Function.Semiconj
      (fun X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ => tensorPhysicalIdOperator X x)
      (fun X => (transposeWithPhysicalMatrix Q).action X)
      (fun X => (transposeWithPhysicalMatrix (physicalIdMatrix Q x)).action X) := by
  intro X
  change tensorPhysicalIdOperator
      (Matrix.tensorPower N Q * Xᵀ * Matrix.tensorPower N Q) x = _
  simp only [transposeWithPhysicalMatrix, operatorId_mul, operatorId_transpose,
    operatorId_tensorPower]

end FiniteChainOperatorSymmetry

/-- Ordinary entrywise conjugation commutes with identity-ancilla attachment
on the full finite-chain operator algebra.
Source: arXiv:1703.09188, conjugation at lines 1005--1010 and
`def:equivalent-symmetry`, lines 1356--1366. -/
theorem conjugationSymmetry_tensorPhysicalId_semiconj (d x N : ℕ) :
    Function.Semiconj
      (fun X : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ => tensorPhysicalIdOperator X x)
      (fun X => (conjugationSymmetry d).action X)
      (fun X => (conjugationSymmetry (d * x)).action X) := by
  intro X
  exact operatorId_map_star X x

end MPOTensor
