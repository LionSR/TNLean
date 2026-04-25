/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Provides `Matrix.blockProjection`, `Matrix.IsBlockDiagonal'`, and the
-- projection-commutant criterion used below.
import TNLean.Algebra.ScalarCommutant
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Block-diagonal commutants from sector projections

This file isolates the algebraic part of the Route B parent-Hamiltonian block
argument.  If the sector projections of a dependent direct sum lie in the span
of a family of matrices and a boundary matrix commutes with that family, then it
commutes with the projections and hence has no off-block entries.

The remaining CF/BNT-specific step is to prove that the sector projections lie
in the finite word span of the assembled tensor.  Once that finite-span input is
available, `MPSTensor.isBlockDiagonal'_of_commutes_reindexed_wordSpan` turns
long-word commutation of the assembled boundary matrix into block diagonality.
-/

open scoped Matrix BigOperators

namespace Matrix

variable {ι α : Type*} {n : ι → Type*}
variable [Fintype ι] [DecidableEq ι]
variable [(i : ι) → Fintype (n i)] [(i : ι) → DecidableEq (n i)]

/-- If every block projection lies in the span of a matrix family `S`, then any
matrix commuting with all members of `S` is block diagonal.

This records the common linearity step used in commutant arguments: commutation
extends from generators to their span, giving commutation with each projection;
`Matrix.isBlockDiagonal'_of_commutes_blockProjection` then kills all off-block
entries. -/
theorem isBlockDiagonal'_of_commutes_span_blockProjection
    {S : α → Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ}
    {X : Matrix ((i : ι) × n i) ((i : ι) × n i) ℂ}
    (hProj : ∀ k : ι,
      blockProjection (n := n) (R := ℂ) k ∈ Submodule.span ℂ (Set.range S))
    (hComm : ∀ a : α, X * S a = S a * X) :
    IsBlockDiagonal' X := by
  classical
  apply isBlockDiagonal'_of_commutes_blockProjection (n := n) (R := ℂ)
  intro k
  have hcomm_span : ∀ M ∈ Submodule.span ℂ (Set.range S), X * M = M * X := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
        rcases hM with ⟨a, rfl⟩
        exact hComm a
    | zero => simp
    | add M N _ _ hM hN => rw [mul_add, add_mul, hM, hN]
    | smul c M _ hM =>
        simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hM]
  exact hcomm_span (blockProjection (n := n) (R := ℂ) k) (hProj k)

end Matrix

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Reindexed word-span version of the block-diagonal commutant criterion.

Let `B` be a tensor whose bond space is the reindexed direct sum
`Fin (∑ k, dim k)`.  Pull all length-`m` word products and the boundary matrix
back to the dependent `Σ`-indexed direct sum via `finSigmaFinEquiv.symm`.  If the
block projections lie in the span of these pulled-back word products, then any
matrix on the assembled bond space commuting with all length-`m` word products
pulls back to a block-diagonal matrix.

For `B = toTensorFromBlocks μ A`, the pulled-back word products are the matrices
`Matrix.blockDiagonal' (fun k => (μ k)^m • evalWord (A k) (List.ofFn ω))` by
`evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal`. -/
theorem isBlockDiagonal'_of_commutes_reindexed_wordSpan
    (B : MPSTensor d (∑ k : Fin r, dim k)) {m : ℕ}
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hProj : ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord B (List.ofFn ω))))
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord B (List.ofFn ω) = evalWord B (List.ofFn ω) * X) :
    Matrix.IsBlockDiagonal'
      (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) := by
  classical
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k : Fin r, dim k) := finSigmaFinEquiv
  apply Matrix.isBlockDiagonal'_of_commutes_span_blockProjection
    (n := fun k : Fin r => Fin (dim k))
    (S := fun ω : Fin m → Fin d => Matrix.reindex e.symm e.symm (evalWord B (List.ofFn ω)))
    hProj
  intro ω
  have h := congrArg (Matrix.reindex e.symm e.symm) (hComm ω)
  simpa [e, Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h

/-- Entrywise off-block-zero corollary of
`isBlockDiagonal'_of_commutes_reindexed_wordSpan`.

This is often the most convenient form when using the result inside a boundary
matrix decomposition proof: after pulling the boundary matrix back to dependent
block coordinates, every entry from block `i` to a distinct block `j` vanishes. -/
theorem offBlock_zero_of_commutes_reindexed_wordSpan
    (B : MPSTensor d (∑ k : Fin r, dim k)) {m : ℕ}
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hProj : ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord B (List.ofFn ω))))
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord B (List.ofFn ω) = evalWord B (List.ofFn ω) * X)
    {i j : Fin r} (hij : i ≠ j) (a : Fin (dim i)) (b : Fin (dim j)) :
    (Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X) ⟨i, a⟩ ⟨j, b⟩ = 0 := by
  have hBD := isBlockDiagonal'_of_commutes_reindexed_wordSpan (B := B) hProj hComm
  exact (Matrix.isBlockDiagonal'_iff_offBlock_zero _).mp hBD hij a b

end MPSTensor
