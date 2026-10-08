/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.BlockAssembly

/-!
# Coordinate resolution of a dependent direct sum

The isometric inclusions of finitely many blocks resolve the identity, and
their adjoints intertwine a weighted block tensor with the selected block.
These exact matrix identities retain the coordinate maps needed when cyclic
sectors of different bond dimensions are assembled into one tensor.

Source: arXiv:1606.00608, equation `II_CF1`, lines 214--225.
-/

open scoped Matrix BigOperators
namespace MPSTensor
variable {d r : ℕ}

/-- The coordinate inclusions resolve the identity of a finite direct sum.
Source: arXiv:1606.00608, equation `II_CF1`, lines 214--225. -/
theorem sum_blockInclusion_mul_conjTranspose (dim : Fin r → ℕ) :
    ∑ j, blockInclusion dim j * (blockInclusion dim j)ᴴ = 1 := by
  let dim' := fun j : Fin r => Fin (dim j)
  let e : ((j : Fin r) × dim' j) ≃ Fin (∑ j, dim j) := finSigmaFinEquiv
  let E := fun j => Matrix.sigmaBlockInclusion dim' j
  have hDiag : Matrix.blockDiagonal' (fun j =>
      (1 : Matrix (dim' j) (dim' j) ℂ)) = 1 := Matrix.blockDiagonal'_one
  have hRaw : ∑ j, E j * (E j)ᴴ = 1 := by
    simpa only [Matrix.mul_one, hDiag, E] using
      (Matrix.blockDiagonal'_eq_sum_sigmaBlockInclusion
      (fun j => (1 : Matrix (dim' j) (dim' j) ℂ))).symm
  have hTerm (j : Fin r) :
      blockInclusion dim j * (blockInclusion dim j)ᴴ =
        Matrix.reindexLinearEquiv ℂ ℂ e e (E j * (E j)ᴴ) := by
    change Matrix.reindex e (Equiv.refl _) (E j) *
      (Matrix.reindex e (Equiv.refl _) (E j))ᴴ = _
    rw [Matrix.conjTranspose_reindex]
    exact Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) e _ _
  simp only [hTerm, ← map_sum, hRaw, Matrix.reindexLinearEquiv_one]

/-- The adjoint coordinate inclusion intertwines a weighted direct sum with
its selected block. Source: arXiv:1606.00608, equation `II_CF1`, lines 214--225. -/
theorem blockInclusion_conjTranspose_mul_toTensorFromBlocks
    {dim : Fin r → ℕ} (μ : Fin r → ℂ) (A : ∀ j, MPSTensor d (dim j))
    (k : Fin r) (i : Fin d) :
    (blockInclusion dim k)ᴴ * toTensorFromBlocks μ A i =
      (μ k • A k i) * (blockInclusion dim k)ᴴ := by
  let dim' := fun j : Fin r => Fin (dim j)
  let e : ((j : Fin r) × dim' j) ≃ Fin (∑ j, dim j) := finSigmaFinEquiv
  let E := Matrix.sigmaBlockInclusion dim' k
  let B := fun j : Fin r => μ j • A j i
  change (Matrix.reindex e (Equiv.refl _) E)ᴴ *
      Matrix.reindex e e (Matrix.blockDiagonal' B) =
        B k * (Matrix.reindex e (Equiv.refl _) E)ᴴ
  rw [Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e Eᴴ *
      Matrix.reindexLinearEquiv ℂ ℂ e e (Matrix.blockDiagonal' B) =
        Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _) (B k) *
          Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e Eᴴ
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) e e,
    Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) (Equiv.refl _) e,
    Matrix.sigmaBlockInclusion_conjTranspose_mul_blockDiagonal']

end MPSTensor

