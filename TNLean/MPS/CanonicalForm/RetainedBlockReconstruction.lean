/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions

/-!
# Inclusions of retained canonical blocks

For a coisometric reconstruction from weighted blocks, each block includes
isometrically into the ambient bond space and intertwines the corresponding
weighted local matrices. These facts apply both to CPSV canonical form and to
the canonical form used for matrix product unitaries.

Source: arXiv:1606.00608, eq. `II_CF1`, lines 214--245, and
arXiv:1703.09188, canonical form, lines 259--265.
-/

open scoped Matrix BigOperators

namespace MPSTensor.RetainedBlockReconstructionData

variable {d D : ℕ} {A : MPSTensor d D}

/-- Multiplying all retained weights multiplies the assembled tensor by the
same scalar. -/
theorem toTensorFromBlocks_mul_weights {r : ℕ} {dim : Fin r → ℕ}
    (c : ℂ) (weights : Fin r → ℂ)
    (blocks : (k : Fin r) → MPSTensor d (dim k)) (i : Fin d) :
    toTensorFromBlocks (fun k => c * weights k) blocks i =
      c • toTensorFromBlocks weights blocks i := by
  ext x y
  simp [toTensorFromBlocks, Matrix.blockDiagonal'_apply, mul_smul]

/-- The isometric inclusion of one retained block into the ambient bond space. -/
noncomputable def ambientBlockInclusion (data : RetainedBlockReconstructionData A)
    (k : Fin data.r) : Matrix (Fin D) (Fin (data.dim k)) ℂ :=
  data.ambient_coisometryᴴ * blockInclusion data.dim k

/-- Each retained block inclusion is an isometry. -/
theorem ambientBlockInclusion_conjTranspose_mul_self
    (data : RetainedBlockReconstructionData A) (k : Fin data.r) :
    (data.ambientBlockInclusion k)ᴴ * data.ambientBlockInclusion k = 1 := by
  rw [ambientBlockInclusion, Matrix.conjTranspose_mul]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc data.ambient_coisometry data.ambient_coisometryᴴ,
    data.coisometric, Matrix.one_mul, blockInclusion_conjTranspose_mul_self]

/-- The reconstruction intertwines an ambient block inclusion with its
weighted canonical block. -/
theorem mul_ambientBlockInclusion (data : RetainedBlockReconstructionData A)
    (k : Fin data.r) (i : Fin d) :
    A i * data.ambientBlockInclusion k =
      data.ambientBlockInclusion k * (data.weights k • data.blocks k i) := by
  rw [data.reconstruct i, ambientBlockInclusion]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc data.ambient_coisometry data.ambient_coisometryᴴ,
    data.coisometric, Matrix.one_mul, toTensorFromBlocks_mul_blockInclusion]

end MPSTensor.RetainedBlockReconstructionData
