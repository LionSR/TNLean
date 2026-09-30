/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Paths between orthogonal isometric embeddings

Two isometries with orthogonal ranges can be joined through isometries by
a plane rotation. If both intertwine the same actions, every point of the
path does as well. This is the physical-space embedding step used in
arXiv:1010.3732, Sections II.B.2 and II.C.2.
-/

namespace Matrix

/-- Rotation between two orthogonal isometric embeddings, with the first
and second embeddings at parameters zero and one. Source context:
arXiv:1010.3732, Sections II.B.2 and II.C.2. -/
noncomputable def orthogonalIsometryPath {m n : Type*}
    (V W : Matrix m n ℂ) (t : ℝ) : Matrix m n ℂ :=
  Real.cos (Real.pi * t / 2) • V + Real.sin (Real.pi * t / 2) • W

/-- Orthogonality of the ranges makes every point of the rotation an
isometry. Source context: arXiv:1010.3732, Section II.B.2. -/
theorem orthogonalIsometryPath_isometry {m n : Type*}
    [Fintype m] [DecidableEq n]
    (V W : Matrix m n ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (hVW : Vᴴ * W = 0) (t : ℝ) :
    (orthogonalIsometryPath V W t)ᴴ * orthogonalIsometryPath V W t = 1 := by
  have hWV : Wᴴ * V = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose hVW
  simp only [orthogonalIsometryPath, conjTranspose_add, conjTranspose_smul,
    star_trivial, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    hV, hW, hVW, hWV, smul_zero, add_zero, zero_add, smul_smul]
  rw [← add_smul]
  rw [← pow_two, ← pow_two, Real.cos_sq_add_sin_sq, one_smul]

@[simp] theorem orthogonalIsometryPath_zero {m n : Type*} (V W : Matrix m n ℂ) :
    orthogonalIsometryPath V W 0 = V := by
  simp [orthogonalIsometryPath]

@[simp] theorem orthogonalIsometryPath_one {m n : Type*} (V W : Matrix m n ℂ) :
    orthogonalIsometryPath V W 1 = W := by
  simp [orthogonalIsometryPath]

/-- The plane rotation varies continuously. Source context:
arXiv:1010.3732, Section II.B.2. -/
theorem continuous_orthogonalIsometryPath {m n : Type*} (V W : Matrix m n ℂ) :
    Continuous (orthogonalIsometryPath V W) := by
  unfold orthogonalIsometryPath
  fun_prop

/-- Linear combinations of intertwining embeddings intertwine the same
physical actions, in particular along the rotation path. Source context:
arXiv:1010.3732, Section II.C.2. -/
theorem orthogonalIsometryPath_intertwining {m n : Type*}
    [Fintype m] [Fintype n]
    (V W : Matrix m n ℂ) (U : Matrix m m ℂ) (R : Matrix n n ℂ)
    (hV : U * V = V * R) (hW : U * W = W * R) (t : ℝ) :
    U * orthogonalIsometryPath V W t = orthogonalIsometryPath V W t * R := by
  simp only [orthogonalIsometryPath, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, hV, hW]

end Matrix
