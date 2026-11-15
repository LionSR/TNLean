/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.PhysicalMatrixSymmetry
import TNLean.MPS.MPU.SymmetryPathTransport

/-!
# Canonical blocking of physical-matrix symmetries

The canonical finite-chain blocking action agrees with the sandwich action
of the blocked local physical matrix. Positive blocking lengths preserve
the set of positive applicable chain lengths. This identifies the explicit
blocked matrices with the blocking operation used in the source definition
of symmetry-preserving equivalence.

Source: arXiv:1703.09188, `def:equivalent-symmetry`, lines 1356--1366.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d : ℕ}

/-- Regrouping a sitewise physical matrix along the canonical blocking
equivalence gives the sitewise power of its local blocked matrix.
Source: arXiv:1703.09188, blocking at lines 297--305. -/
theorem sitewisePhysicalMatrix_blockKron_reindex
    (Q : Matrix (Fin d) (Fin d) ℂ) (N k : ℕ) :
    Matrix.reindex (MPSTensor.blockedConfigEquiv d N k).symm
        (MPSTensor.blockedConfigEquiv d N k).symm (sitewisePhysicalMatrix Q (N * k)) =
      sitewisePhysicalMatrix (MPSTensor.blockKron k Q) N := by
  classical
  symm
  exact Matrix.ext fun σ τ => by
    simpa [sitewisePhysicalMatrix, MPSTensor.blockKron, Matrix.reindex_apply,
      MPSTensor.blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry, Function.comp,
      Fintype.prod_prod_type] using
      (finProdFinEquiv.prod_comp (fun v : Fin (N * k) =>
        Q (MPSTensor.blockedConfigEquiv d N k σ v)
          (MPSTensor.blockedConfigEquiv d N k τ v)))

private theorem symmetry_eq {n : ℕ} (S T : FiniteChainOperatorSymmetry n)
    (happlicable : S.applicable = T.applicable)
    (haction : ∀ N (X : Matrix (Fin N → Fin n) (Fin N → Fin n) ℂ),
      S.action X = T.action X) : S = T := by
  rcases S with ⟨A, f⟩
  rcases T with ⟨B, g⟩
  change A = B at happlicable
  subst B
  have hfg : f = g := by
    funext N X
    exact haction N X
  cases hfg
  rfl

private theorem reindex_mul {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (X Y : Matrix α α ℂ) :
    Matrix.reindex e e (X * Y) = Matrix.reindex e e X * Matrix.reindex e e Y :=
  (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e X Y).symm

namespace FiniteChainOperatorSymmetry

/-- Canonical positive blocking of the physical-matrix adjunction action
is the action of its blocked local matrix, on the entire operator algebra.
Source: arXiv:1703.09188, `def:equivalent-symmetry`, line 1366. -/
theorem daggerWithPhysicalMatrix_block (Q : Matrix (Fin d) (Fin d) ℂ)
    {k : ℕ} (hk : 0 < k) :
    (daggerWithPhysicalMatrix Q).block k =
      daggerWithPhysicalMatrix (MPSTensor.blockKron k Q) := by
  apply symmetry_eq
  · ext N
    simp [block, daggerWithPhysicalMatrix, Nat.mul_pos_iff, hk]
  · intro N X
    simp only [block, daggerWithPhysicalMatrix, reindex_mul,
      sitewisePhysicalMatrix_blockKron_reindex, Matrix.conjTranspose_reindex]
    congr 2
    ext σ τ
    simp [Matrix.reindex_apply]

/-- Canonical positive blocking of the physical-matrix transposition
action is the action of its blocked local matrix.
Source: arXiv:1703.09188, `def:equivalent-symmetry`, line 1366. -/
theorem transposeWithPhysicalMatrix_block (Q : Matrix (Fin d) (Fin d) ℂ)
    {k : ℕ} (hk : 0 < k) :
    (transposeWithPhysicalMatrix Q).block k =
      transposeWithPhysicalMatrix (MPSTensor.blockKron k Q) := by
  apply symmetry_eq
  · ext N
    simp [block, transposeWithPhysicalMatrix, Nat.mul_pos_iff, hk]
  · intro N X
    simp only [block, transposeWithPhysicalMatrix, reindex_mul,
      sitewisePhysicalMatrix_blockKron_reindex]
    congr 2
    ext σ τ
    simp [Matrix.reindex_apply, Matrix.transpose_apply]

/-- The identity physical matrix gives ordinary adjunction. -/
@[simp] theorem daggerWithPhysicalMatrix_one (d : ℕ) :
    daggerWithPhysicalMatrix (1 : Matrix (Fin d) (Fin d) ℂ) = daggerSymmetry d := by
  apply symmetry_eq _ _ rfl
  intro N X
  simp [daggerWithPhysicalMatrix, daggerSymmetry, sitewisePhysicalMatrix_one]

/-- The identity physical matrix gives ordinary transposition. -/
@[simp] theorem transposeWithPhysicalMatrix_one (d : ℕ) :
    transposeWithPhysicalMatrix (1 : Matrix (Fin d) (Fin d) ℂ) = transposeSymmetry d := by
  apply symmetry_eq _ _ rfl
  intro N X
  simp [transposeWithPhysicalMatrix, transposeSymmetry, sitewisePhysicalMatrix_one]

end FiniteChainOperatorSymmetry

/-- Canonical positive blocking preserves ordinary entrywise conjugation.
Source: arXiv:1703.09188, `def:equivalent-symmetry`, line 1366. -/
theorem conjugationSymmetry_block {k : ℕ} (hk : 0 < k) :
    (conjugationSymmetry d).block k =
      conjugationSymmetry (MPSTensor.blockPhysDim d k) := by
  apply symmetry_eq
  · ext N
    simp [FiniteChainOperatorSymmetry.block, conjugationSymmetry, Nat.mul_pos_iff, hk]
  · intro N X
    ext σ τ
    simp [FiniteChainOperatorSymmetry.block, conjugationSymmetry,
      Matrix.reindex_apply, Matrix.map_apply]

end MPOTensor
