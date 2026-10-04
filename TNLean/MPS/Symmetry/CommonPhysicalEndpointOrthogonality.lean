/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.CommonPhysicalEndpoints

/-!
# Orthogonal original physical spaces in the common representation

The occupied polar frames of the two original tensors enter disjoint
matrix-unit sectors of the common physical space. Their orthogonal
complements enter separate spectator summands. Consequently the full
physical embeddings of the original spaces have orthogonal images.

Source: arXiv:1010.3732, Section II.C, enlargement of the physical Hilbert
space, and Section II.F.2, equation eq:1d-sym:jointsym.
-/

open scoped Matrix

namespace MPSTensor

private theorem physicalSumInclusion_conjTranspose_mul_frame
    {m d r : ℕ} (F : Matrix (Fin d) (Fin r) ℂ)
    (W : Matrix (Fin m) (Fin r) ℂ) :
    (physicalSumInclusion m d)ᴴ * Matrix.finIsometricFrameEmbedding F W = W * Fᴴ := by
  rw [physicalSumInclusion, Matrix.finIsometricFrameEmbedding,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  simp only [Matrix.isometricFrameEmbedding,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.submatrix_id_id]

private theorem sptPhysicalEmbedding_left_conjTranspose_mul_right
    (D₀ D₁ : ℕ) :
    (Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₀) (Fin.castAddEmb D₁)))ᴴ *
        Matrix.coordinateInclusion (sptPhysicalEmbedding (D := D₁) (Fin.natAddEmb D₀)) =
      (0 : Matrix (Fin (D₀ * D₀)) (Fin (D₁ * D₁)) ℂ) := by
  rw [Matrix.conjTranspose_coordinateInclusion_mul]
  ext p q
  have hne : sptPhysicalEmbedding (Fin.castAddEmb D₁) p ≠
      sptPhysicalEmbedding (Fin.natAddEmb D₀) q := by
    intro h
    have hpair := finProdFinEquiv.injective h
    have hfirst := congrArg (fun x : Fin (D₀ + D₁) × Fin (D₀ + D₁) => x.1.val) hpair
    change (finProdFinEquiv.symm p).1.val = D₀ + (finProdFinEquiv.symm q).1.val at hfirst
    omega
  simp only [Matrix.submatrix_apply, Matrix.coordinateInclusion, id_eq, ite_eq_right hne,
    Matrix.zero_apply]

private theorem frame_conjTranspose_mul_physicalSumInclusion
    {m d r : ℕ} (F : Matrix (Fin d) (Fin r) ℂ)
    (W : Matrix (Fin m) (Fin r) ℂ) :
    (Matrix.finIsometricFrameEmbedding F W)ᴴ * physicalSumInclusion m d = F * Wᴴ := by
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
    congrArg Matrix.conjTranspose (physicalSumInclusion_conjTranspose_mul_frame F W)

/-- The full physical embeddings of the two original tensors have
orthogonal images. The assertion is independent of injectivity: the
occupied target frames are disjoint, and the retained complements lie in
different spectator summands. Source: arXiv:1010.3732, Section II.C,
lines 447--465, and Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem commonPhysicalEmbeddingLeft_conjTranspose_mul_right_eq_zero
    {d₀ d₁ D₀ D₁ : ℕ} (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁) :
    (commonPhysicalEmbeddingLeft d₁ D₁ A₀)ᴴ *
        commonPhysicalEmbeddingRight d₀ D₀ A₁ = 0 := by
  simp only [commonPhysicalEmbeddingLeft, commonPhysicalEmbeddingRight, polarFrameEmbedding,
    Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, physicalSumInclusion_conjTranspose_mul_frame]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, frame_conjTranspose_mul_physicalSumInclusion]
  rw [Matrix.mul_assoc (polarIsoMatrix A₀), sptPhysicalEmbedding_left_conjTranspose_mul_right,
    Matrix.mul_zero, Matrix.zero_mul]

end MPSTensor
