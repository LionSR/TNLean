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
theorem tensorPower_blockKron_reindex
    (Q : Matrix (Fin d) (Fin d) ℂ) (N k : ℕ) :
    Matrix.reindex (MPSTensor.blockedConfigEquiv d N k).symm
        (MPSTensor.blockedConfigEquiv d N k).symm (Matrix.tensorPower (N * k) Q) =
      Matrix.tensorPower N (MPSTensor.blockKron k Q) := by
  classical
  symm
  exact Matrix.ext fun σ τ => by
    simpa [Matrix.tensorPower_apply, MPSTensor.blockKron, Matrix.reindex_apply,
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
  have hfg : @f = @g := by
    funext N X
    exact haction N X
  cases hfg
  rfl

private theorem reindex_mul {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (X Y : Matrix α α ℂ) :
    Matrix.reindex e e (X * Y) = Matrix.reindex e e X * Matrix.reindex e e Y :=
  (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e X Y).symm

private theorem block_applicable_pos (S : FiniteChainOperatorSymmetry d)
    (hS : S.applicable = {N | 0 < N}) {k : ℕ} (hk : 0 < k) :
    (S.block k).applicable = {N | 0 < N} := by
  ext N
  change (N * k ∈ S.applicable) ↔ 0 < N
  rw [hS]
  exact Nat.mul_pos_iff_of_pos_right hk

namespace FiniteChainOperatorSymmetry

/-- The canonically blocked adjunction action tested on every positive blocked
chain length. At blocking length zero, the positive-chain convention is retained
rather than taking the inverse image of the original applicable lengths.
Source: arXiv:1703.09188, `SSymmetries-dagger` and `def:equivalent-symmetry`. -/
noncomputable def blockedDaggerWithPhysicalMatrix
    (Q : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    FiniteChainOperatorSymmetry (MPSTensor.blockPhysDim d k) :=
  { (daggerWithPhysicalMatrix Q).block k with applicable := {N | 0 < N} }

/-- The canonically blocked transposition action, with the same positive-chain
convention at blocking length zero as the explicit blocked local matrix.
Source: arXiv:1703.09188, `SSymmetries-transpose` and `def:equivalent-symmetry`. -/
noncomputable def blockedTransposeWithPhysicalMatrix
    (Q : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    FiniteChainOperatorSymmetry (MPSTensor.blockPhysDim d k) :=
  { (transposeWithPhysicalMatrix Q).block k with applicable := {N | 0 < N} }

/-- The positive-chain blocked action is exactly the sandwich action of the
blocked local matrix, including blocking length zero.
Source: arXiv:1703.09188, blocking at lines 297--305. -/
theorem blockedDaggerWithPhysicalMatrix_eq
    (Q : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    blockedDaggerWithPhysicalMatrix Q k =
      daggerWithPhysicalMatrix (MPSTensor.blockKron k Q) := by
  apply symmetry_eq
  · rfl
  · intro N X
    simp only [blockedDaggerWithPhysicalMatrix, block, daggerWithPhysicalMatrix,
      reindex_mul, tensorPower_blockKron_reindex,
      Matrix.conjTranspose_reindex]
    congr 2
    ext σ τ
    simp [Matrix.reindex_apply]

/-- The transposition analogue of the full blocked-matrix action identity.
Source: arXiv:1703.09188, blocking at lines 297--305. -/
theorem blockedTransposeWithPhysicalMatrix_eq
    (Q : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) :
    blockedTransposeWithPhysicalMatrix Q k =
      transposeWithPhysicalMatrix (MPSTensor.blockKron k Q) := by
  apply symmetry_eq
  · rfl
  · intro N X
    simp only [blockedTransposeWithPhysicalMatrix, block, transposeWithPhysicalMatrix,
      reindex_mul, tensorPower_blockKron_reindex]
    congr 2
    ext σ τ
    simp [Matrix.reindex_apply, Matrix.transpose_apply]

/-- Canonical positive blocking of the physical-matrix adjunction action
is the action of its blocked local matrix, on the entire operator algebra.
Source: arXiv:1703.09188, `def:equivalent-symmetry`, line 1366. -/
theorem daggerWithPhysicalMatrix_block (Q : Matrix (Fin d) (Fin d) ℂ)
    {k : ℕ} (hk : 0 < k) :
    (daggerWithPhysicalMatrix Q).block k =
      daggerWithPhysicalMatrix (MPSTensor.blockKron k Q) := by
  calc
    _ = blockedDaggerWithPhysicalMatrix Q k := by
      apply symmetry_eq
      · exact block_applicable_pos _ rfl hk
      · intro N X
        rfl
    _ = _ := blockedDaggerWithPhysicalMatrix_eq Q k

/-- Canonical positive blocking of the physical-matrix transposition
action is the action of its blocked local matrix.
Source: arXiv:1703.09188, `def:equivalent-symmetry`, line 1366. -/
theorem transposeWithPhysicalMatrix_block (Q : Matrix (Fin d) (Fin d) ℂ)
    {k : ℕ} (hk : 0 < k) :
    (transposeWithPhysicalMatrix Q).block k =
      transposeWithPhysicalMatrix (MPSTensor.blockKron k Q) := by
  calc
    _ = blockedTransposeWithPhysicalMatrix Q k := by
      apply symmetry_eq
      · exact block_applicable_pos _ rfl hk
      · intro N X
        rfl
    _ = _ := blockedTransposeWithPhysicalMatrix_eq Q k

/-- The identity physical matrix gives ordinary adjunction. -/
@[simp] theorem daggerWithPhysicalMatrix_one (d : ℕ) :
    daggerWithPhysicalMatrix (1 : Matrix (Fin d) (Fin d) ℂ) = daggerSymmetry d := by
  apply symmetry_eq (daggerWithPhysicalMatrix (1 : Matrix (Fin d) (Fin d) ℂ))
    (daggerSymmetry d) rfl
  intro N X
  simp [daggerWithPhysicalMatrix, daggerSymmetry, Matrix.tensorPower_one]

/-- The identity physical matrix gives ordinary transposition. -/
@[simp] theorem transposeWithPhysicalMatrix_one (d : ℕ) :
    transposeWithPhysicalMatrix (1 : Matrix (Fin d) (Fin d) ℂ) = transposeSymmetry d := by
  apply symmetry_eq (transposeWithPhysicalMatrix (1 : Matrix (Fin d) (Fin d) ℂ))
    (transposeSymmetry d) rfl
  intro N X
  simp [transposeWithPhysicalMatrix, transposeSymmetry, Matrix.tensorPower_one]

end FiniteChainOperatorSymmetry

/-- Canonical positive blocking preserves ordinary entrywise conjugation.
Source: arXiv:1703.09188, `def:equivalent-symmetry`, line 1366. -/
theorem conjugationSymmetry_block {k : ℕ} (hk : 0 < k) :
    (conjugationSymmetry d).block k =
      conjugationSymmetry (MPSTensor.blockPhysDim d k) := by
  apply symmetry_eq
  · exact block_applicable_pos _ rfl hk
  · intro N X
    ext σ τ
    simp [FiniteChainOperatorSymmetry.block, conjugationSymmetry,
      Matrix.reindex_apply, Matrix.map_apply]

end MPOTensor
