/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Scalar relations from entrywise conjugates of unitary matrices

This file proves the generic unitary-matrix algebra used for the virtual-gauge signs in
FBC25, equations `eq:defT` and `eq:intro_sigma` (arXiv:2502.20257, lines 1557--1564).
The operation on the second matrix is entrywise complex conjugation
`Matrix.map (starRingEnd ℂ)`, not conjugate transpose.

These results are conditional on the scalar-matrix relations. They do not construct the
virtual gauges or prove those relations for an MPU representation.

## Main results

- `Matrix.scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one`: the scalar multiplying the
  identity in a product of unitaries has unit modulus.
- `Matrix.paired_scalars_mul_eq_one_of_mul_map_star_eq_smul_one`: scalars from the two
  oppositely ordered relations are reciprocal.
- `Matrix.scalar_eq_one_or_neg_one_of_mul_map_star_self_eq_smul_one`: the scalar in the
  self relation is a sign.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- If the product of a unitary matrix and the entrywise conjugate of another unitary
matrix is scalar, then the scalar has unit modulus. This is the scalar phase step in
FBC25, equation `eq:intro_sigma` (arXiv:2502.20257, lines 1559--1562). -/
theorem scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one
    (T S : Matrix.unitaryGroup n ℂ) (σ : ℂ)
    (hσ : (T : Matrix n n ℂ) * (S : Matrix n n ℂ).map (starRingEnd ℂ) = σ • 1) :
    σ * starRingEnd ℂ σ = 1 := by
  let i : n := Classical.choice inferInstance
  have hmem : (σ • 1 : Matrix n n ℂ) ∈ Matrix.unitaryGroup n ℂ := by
    rw [← hσ]
    exact (Matrix.unitaryGroup n ℂ).mul_mem T.property
      (Matrix.map_star_mem_unitaryGroup_iff.mpr S.property)
  have hunit := Matrix.mem_unitaryGroup_iff.mp hmem
  have hii := congrFun (congrFun hunit i) i
  simpa [Matrix.mul_apply, Matrix.one_apply] using hii

/-- For two unitary matrices, scalars in the two relations obtained by exchanging the
matrices and entrywise conjugating the second factor are reciprocal. This is the identity
`σ_g σ_{g⁻¹} = 1` following FBC25, equation `eq:intro_sigma`
(arXiv:2502.20257, lines 1559--1563). -/
theorem paired_scalars_mul_eq_one_of_mul_map_star_eq_smul_one
    (T S : Matrix.unitaryGroup n ℂ) (σ τ : ℂ)
    (hσ : (T : Matrix n n ℂ) * (S : Matrix n n ℂ).map (starRingEnd ℂ) = σ • 1)
    (hτ : (S : Matrix n n ℂ) * (T : Matrix n n ℂ).map (starRingEnd ℂ) = τ • 1) :
    σ * τ = 1 := by
  let Sstar := Matrix.UnitaryGroup.map_star S
  have hcomm : (Sstar : Matrix n n ℂ) * (T : Matrix n n ℂ) = σ • 1 := by
    calc
      (Sstar : Matrix n n ℂ) * (T : Matrix n n ℂ) =
          (1 : Matrix n n ℂ) * ((Sstar : Matrix n n ℂ) * (T : Matrix n n ℂ)) := by simp
      _ = (((T⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) * (T : Matrix n n ℂ)) *
          ((Sstar : Matrix n n ℂ) * (T : Matrix n n ℂ)) := by simp
      _ = ((T⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) *
          (((T : Matrix n n ℂ) * (Sstar : Matrix n n ℂ)) * (T : Matrix n n ℂ)) := by
            simp only [mul_assoc]
      _ = ((T⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) *
          ((σ • 1 : Matrix n n ℂ) * (T : Matrix n n ℂ)) := by
            rw [show (T : Matrix n n ℂ) * (Sstar : Matrix n n ℂ) = σ • 1 by
              simpa [Sstar] using hσ]
      _ = σ • 1 := by simp
  have hτstar : (Sstar : Matrix n n ℂ) * (T : Matrix n n ℂ) = starRingEnd ℂ τ • 1 := by
    have h := congrArg (fun M : Matrix n n ℂ ↦ M.map (starRingEnd ℂ)) hτ
    rw [Matrix.map_mul] at h
    ext i j
    have hij := congrFun (congrFun h i) j
    by_cases hij' : i = j <;>
      simpa [Sstar, Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply, Function.comp_apply, hij']
        using hij
  have hστ : σ = starRingEnd ℂ τ := by
    let i : n := Classical.choice inferInstance
    have h := congrFun (congrFun (hcomm.symm.trans hτstar) i) i
    simpa using h
  have hτunit := scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one S T τ hτ
  rw [hστ, mul_comm]
  exact hτunit

/-- In the self relation, the scalar multiplying the identity is `1` or `-1`. This is the
involution conclusion after FBC25, equation `eq:intro_sigma`
(arXiv:2502.20257, lines 1563--1564). -/
theorem scalar_eq_one_or_neg_one_of_mul_map_star_self_eq_smul_one
    (T : Matrix.unitaryGroup n ℂ) (σ : ℂ)
    (hσ : (T : Matrix n n ℂ) * (T : Matrix n n ℂ).map (starRingEnd ℂ) = σ • 1) :
    σ = 1 ∨ σ = -1 := by
  apply sq_eq_one_iff.mp
  rw [pow_two]
  exact paired_scalars_mul_eq_one_of_mul_map_star_eq_smul_one T T σ σ hσ hσ

end Matrix
