/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.BlockAssembly
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Unitary assembly of an isometric block decomposition

A family of isometries whose range projections sum to the identity identifies
the original space unitarily with the direct sum of their domains. This
identification carries every block-diagonal matrix to its sum of compressed
corners, including independently weighted corners.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary` and Theorem 4.1,
lines 765--806.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- The flattened block-diagonal matrix is the sum of its coordinate
corners. Source: arXiv:1606.00608, eq. `II_CF1`, lines 214--225. -/
theorem reindex_blockDiagonal_eq_sum_blockInclusion
    {r : ℕ} {dim : Fin r → ℕ}
    (B : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) :
    Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv (Matrix.blockDiagonal' B) =
      ∑ k, blockInclusion dim k * B k * (blockInclusion dim k)ᴴ := by
  classical
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k, dim k) := finSigmaFinEquiv
  have h := congrArg (Matrix.reindexLinearEquiv ℂ ℂ e e)
    (Matrix.blockDiagonal'_eq_sum_sigmaBlockInclusion B)
  rw [map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
  simp only [blockInclusion, Matrix.conjTranspose_reindex]
  change Matrix.reindexLinearEquiv ℂ ℂ e e
      (Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k * B k *
        (Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k)ᴴ) =
    Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _)
        (Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) (Equiv.refl _) (B k) *
      Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e
        (Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k)ᴴ
  rw [Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) (Equiv.refl _),
    Matrix.reindexLinearEquiv_mul ℂ ℂ e (Equiv.refl _) e]

/-- The coordinate inclusions resolve the identity of the flattened bond
space. Source: arXiv:1606.00608, eq. `II_CF1`, lines 214--225. -/
theorem sum_blockInclusion_mul_conjTranspose {r : ℕ} (dim : Fin r → ℕ) :
    ∑ k, blockInclusion dim k * (blockInclusion dim k)ᴴ = 1 := by
  simpa [← Pi.one_def, Matrix.reindex_apply] using
    (reindex_blockDiagonal_eq_sum_blockInclusion (fun k => (1 : Matrix (Fin (dim k))
      (Fin (dim k)) ℂ))).symm

/-- Letterwise reconstruction of a weighted block tensor from its coordinate
corners. Source: arXiv:1606.00608, eq. `II_CF1`, lines 214--225. -/
theorem toTensorFromBlocks_eq_sum_blockInclusion
    {d r : ℕ} {dim : Fin r → ℕ} (μ : Fin r → ℂ)
    (A : (k : Fin r) → MPSTensor d (dim k)) (i : Fin d) :
    toTensorFromBlocks μ A i =
      ∑ k, blockInclusion dim k * (μ k • A k i) * (blockInclusion dim k)ᴴ :=
  reindex_blockDiagonal_eq_sum_blockInclusion _

/-- Isometric block inclusions resolving the identity assemble into one
unitary, simultaneously for every family of matrices on the blocks.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary` and Theorem 4.1,
lines 765--806. -/
theorem exists_unitary_of_isometric_block_decomposition
    {r D : ℕ} {dim : Fin r → ℕ}
    (V : (k : Fin r) → Matrix (Fin D) (Fin (dim k)) ℂ)
    (hV : ∀ k, (V k)ᴴ * V k = 1)
    (hsum : ∑ k, V k * (V k)ᴴ = 1) :
    ∃ Y : Matrix (Fin D) (Fin (∑ k, dim k)) ℂ,
      Y * Yᴴ = 1 ∧ Yᴴ * Y = 1 ∧
      ∀ B : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
        Y * Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv (Matrix.blockDiagonal' B) * Yᴴ =
          ∑ k, V k * B k * (V k)ᴴ := by
  classical
  let W : Matrix (Fin D) ((k : Fin r) × Fin (dim k)) ℂ := fun i x => V x.1 i x.2
  have hWW : W * Wᴴ = 1 := by
    ext i j
    change (∑ x : (k : Fin r) × Fin (dim k), V x.1 i x.2 * star (V x.1 j x.2)) = _
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sigma,
      Matrix.sum_apply] using congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M i j) hsum
  have hdim : ∑ k, dim k = D := by
    have h := congrArg Matrix.trace hsum
    simp only [Matrix.trace_sum, Matrix.trace_mul_comm, hV, Matrix.trace_one,
      Fintype.card_fin] at h
    exact_mod_cast h
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k, dim k) := finSigmaFinEquiv
  let Y := Matrix.reindex (Equiv.refl (Fin D)) e W
  have hYstar : Yᴴ = Matrix.reindex e (Equiv.refl (Fin D)) Wᴴ :=
    Matrix.conjTranspose_reindex _ _ _
  have hYY : Y * Yᴴ = 1 := by
    rw [hYstar]
    change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e W *
      Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) Wᴴ = 1
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) e (Equiv.refl _)]
    simpa only [Matrix.reindexLinearEquiv_refl_refl, LinearEquiv.refl_apply] using hWW
  refine ⟨Y, hYY, ?_, ?_⟩
  · exact (Matrix.mul_eq_one_comm_of_equiv (finCongr hdim.symm)).mp hYY
  · intro B
    have hWE (k : Fin r) : W * Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k = V k := by
      ext i j
      change (∑ x : (k : Fin r) × Fin (dim k),
        V x.1 i x.2 * (if x = ⟨k, j⟩ then 1 else 0)) = V k i j
      simp
    have hraw : W * Matrix.blockDiagonal' B * Wᴴ = ∑ k, V k * B k * (V k)ᴴ := by
      rw [Matrix.blockDiagonal'_eq_sum_sigmaBlockInclusion, Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      calc W * (Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k * B k *
              (Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k)ᴴ) * Wᴴ =
            (W * Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k) * B k *
              (W * Matrix.sigmaBlockInclusion (fun j => Fin (dim j)) k)ᴴ := by
                simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hWE]
    rw [hYstar]
    change Matrix.reindexLinearEquiv ℂ ℂ (Equiv.refl _) e W *
        Matrix.reindexLinearEquiv ℂ ℂ e e (Matrix.blockDiagonal' B) *
        Matrix.reindexLinearEquiv ℂ ℂ e (Equiv.refl _) Wᴴ = _
    rw [Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) e e,
      Matrix.reindexLinearEquiv_mul ℂ ℂ (Equiv.refl _) e (Equiv.refl _)]
    exact hraw

end MPSTensor
