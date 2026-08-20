/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixMulRange

/-!
# Compatibility names for matrix left-multiplication ranges

This module provides the original `MPSTensor` names for the neutral matrix API in
`TNLean.Algebra.MatrixMulRange`, preserving existing rectangular-span arguments.
-/

open scoped Matrix

namespace MPSTensor

variable {D : ℕ}

/-- Compatibility name for `Matrix.col_mul`. -/
lemma col_mul (P X : Matrix (Fin D) (Fin D) ℂ) (j : Fin D) :
    (P * X).col j = P *ᵥ (X.col j) :=
  Matrix.col_mul P X j

/-- Compatibility name for `Matrix.mem_range_mulLeft_iff_cols`. -/
theorem mem_range_mulLeft_iff_cols
    (P : Matrix (Fin D) (Fin D) ℂ)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    M ∈ LinearMap.range (LinearMap.mulLeft ℂ P) ↔
      ∀ j : Fin D, M.col j ∈ LinearMap.range (Matrix.toLin' P) :=
  Matrix.mem_range_mulLeft_iff_cols P M

/-- Compatibility name for `Matrix.colRangeSubmodule`. -/
noncomputable def colRangeSubmodule (P : Matrix (Fin D) (Fin D) ℂ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.colRangeSubmodule P

/-- Compatibility name for `Matrix.colRangeSubmoduleEquiv`. -/
noncomputable def colRangeSubmoduleEquiv (P : Matrix (Fin D) (Fin D) ℂ) :
    colRangeSubmodule (D := D) P ≃ₗ[ℂ]
      (Fin D → LinearMap.range (Matrix.toLin' P)) :=
  Matrix.colRangeSubmoduleEquiv P

/-- Compatibility name for `Matrix.range_mulLeft_eq_pi`. -/
theorem range_mulLeft_eq_pi (P : Matrix (Fin D) (Fin D) ℂ) :
    LinearMap.range (LinearMap.mulLeft ℂ P) = colRangeSubmodule (D := D) P :=
  Matrix.range_mulLeft_eq_pi P

/-- Compatibility name for `Matrix.finrank_range_mulLeft`. -/
theorem finrank_range_mulLeft
    (P : Matrix (Fin D) (Fin D) ℂ) :
    Module.finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ P)) = D * Matrix.rank P :=
  Matrix.finrank_range_mulLeft P

end MPSTensor
