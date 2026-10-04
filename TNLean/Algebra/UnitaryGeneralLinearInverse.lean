/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Inverses of unitary general linear matrices

A general linear matrix whose underlying complex matrix is unitary has
its conjugate transpose as inverse. This permits the virtual matrices of
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym, to be used
both as general linear and as unitary matrices without repeating the
inverse calculation.
-/

open scoped Matrix
namespace Matrix

/-- The general linear inverse of a unitary matrix is its conjugate
transpose. This is a general matrix identity used for the virtual pair
actions in arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : GL ι ℂ)
    (hX : (X : Matrix ι ι ℂ) ∈ unitaryGroup ι ℂ) :
    ((X⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) = (X : Matrix ι ι ℂ)ᴴ := by
  rw [coe_units_inv, ← star_eq_conjTranspose]
  exact inv_eq_left_inv (mem_unitaryGroup_iff'.mp hX)

end Matrix
