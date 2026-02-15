import MPSLean.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Block

open scoped Matrix BigOperators

namespace MPSTensor

/-- A canonical form for an MPS tensor: block diagonal with normal blocks.

This is a lightweight data structure which will be used later to state and prove the multi-block
version of the Fundamental Theorem. -/
structure CanonicalForm (d : ℕ) where
  /-- Number of blocks -/
  numBlocks : ℕ
  /-- Bond dimension of each block -/
  blockDim : Fin numBlocks → ℕ
  /-- The normal tensor for each block -/
  blockTensor : (k : Fin numBlocks) → MPSTensor d (blockDim k)
  /-- Scaling factor for each block -/
  μ : Fin numBlocks → ℂ
  /-- Each block tensor is injective (the algebraic normality condition) -/
  block_injective : ∀ k, MPSTensor.IsInjective (blockTensor k)

namespace CanonicalForm

variable {d : ℕ} (C : CanonicalForm d)

/-- Total bond dimension of the block-diagonal tensor. -/
noncomputable def totalDim : ℕ := ∑ k : Fin C.numBlocks, C.blockDim k

/-- Turn a canonical form into an actual MPS tensor by putting the blocks on the diagonal.

We use the dependent block-diagonal construction `Matrix.blockDiagonal'`, and then reindex the
resulting `Σ`-indexed matrix as a `Fin (∑ k, blockDim k)`-indexed matrix using
`finSigmaFinEquiv`. -/
noncomputable def toTensor : MPSTensor d C.totalDim := fun i : Fin d =>
  let blocks : (k : Fin C.numBlocks) → Matrix (Fin (C.blockDim k)) (Fin (C.blockDim k)) ℂ :=
    fun k => (C.μ k) • (C.blockTensor k i)
  let BD :
      Matrix ((k : Fin C.numBlocks) × Fin (C.blockDim k))
        ((k : Fin C.numBlocks) × Fin (C.blockDim k)) ℂ :=
    Matrix.blockDiagonal' blocks
  let e : ((k : Fin C.numBlocks) × Fin (C.blockDim k)) ≃ Fin C.totalDim :=
    (finSigmaFinEquiv (m := C.numBlocks) (n := C.blockDim))
  (Matrix.reindex e e) BD

end CanonicalForm

end MPSTensor
