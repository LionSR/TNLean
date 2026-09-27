/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.FNWDimensionConstant.MatrixUnitPaths

/-!
# Normalization and orthogonality from scalar path sums

The inner-product formulas for marked paths turn scalar contractions into
unit-vector and ground-space orthogonality certificates.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor.FNWDimensionConstant

variable {k : ℕ}

/-- A unit scalar self-contraction normalizes a marked path vector. -/
theorem norm_pathVector_eq_one (t z : Matrix (Fin k) (Fin k) ℝ) (a f : Fin k)
    (h : (∑ b, ∑ c, ∑ e, z b e * z b e *
      (t a b * t b c * t c e * t e f) ^ 2 : ℝ) = 1) :
    ‖pathVector t z a f‖ = 1 := by
  have hi := inner_pathVector t z z a f
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hi, h, Complex.ofReal_one,
    RCLike.one_re, Real.sqrt_one]

/-- A vanishing scalar contraction makes a marked path perpendicular to the
full-interval ground space. -/
theorem pathVector_mem_groundSpaceES_orthogonal
    (t z : Matrix (Fin k) (Fin k) ℝ) (a f : Fin k)
    (h : (∑ b, ∑ c, ∑ e, z b e *
      (t a b * t b c * t c e * t e f) ^ 2 : ℝ) = 0) :
    pathVector t z a f ∈ (groundSpaceES (matrixUnitTensor t) 4)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨X, hX⟩ := (mem_groundSpaceES_iff (matrixUnitTensor t) 4 u).mp hu
  have huX : WithLp.toLp 2 (groundSpaceMap (matrixUnitTensor t) 4 X) = u :=
    congrArg (WithLp.toLp 2) hX
  simpa only [huX, h, Complex.ofReal_zero, zero_mul] using
    inner_pathVector_groundSpaceMap t z X a f

end MPSTensor.FNWDimensionConstant
