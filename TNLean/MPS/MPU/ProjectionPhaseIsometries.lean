/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Interval isometries for a product-projection phase gate

For orthogonal one-site projections, consider `U = I + (z - 1) P`, where
`P` is their tensor product and `star z * z = 1`. The bond-two representation
with letters `I,P` admits interval isometries whose merge contraction has
norm two independently of `z`. Its boundary frames need not lie in the
exterior density-operator Gram sets used in arXiv:2508.08160v2.

This module proves the normalization of the prefix, interior, and suffix
maps, the bond contraction identity, invertibility of the boundary frames,
and the squared merge norm. These are matrix statements; the recursive
circuit construction and its gate count are not formalized here.

The construction is derived in `docs/audits/2026-10-02_mpu_tree_conditioning.tex`.
Source context: arXiv:2508.08160v2, `references/2508.08160/main.tex`,
MPO-projector unitaries at line 817, the exterior Gram sets of
Lemma `lem:isometries`, lines 1756--1818, and Merging Lemma `lem:merging`,
lines 2145--2156. The boundary frames below are an additional construction,
rather than a formalization of those Gram sets.
-/

open scoped Matrix
open Matrix
namespace MPUCircuit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem projection_gram (P : Matrix ι ι ℂ) (hP : IsStarProjection P) (a b : ℂ) :
    (a • (1 : Matrix ι ι ℂ) + b • P)ᴴ * (a • 1 + b • P) =
      (star a * a) • 1 + (star a * b + star b * a + star b * b) • P := by
  simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_one,
    hP.isSelfAdjoint.isHermitian.eq, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    one_mul, mul_one, hP.isIdempotentElem.eq, add_smul, mul_comm, add_assoc, add_left_comm]

/-- The suffix isometry has components `I + (z - 1) P / 2` and `(z - 1) P / 2`. -/
noncomputable def projectionSuffixMap (P : Matrix ι ι ℂ) (z : ℂ) : Matrix (ι ⊕ ι) ι ℂ :=
  fromRows (1 + ((z - 1) / 2) • P) (((z - 1) / 2) • P)

/-- A unit-modulus phase gives a normalized suffix map. -/
theorem projectionSuffixMap_isIsometry (P : Matrix ι ι ℂ) (hP : IsStarProjection P)
    (z : ℂ) (hz : star z * z = 1) :
    (projectionSuffixMap P z).IsIsometry := by
  change (projectionSuffixMap P z)ᴴ * projectionSuffixMap P z = 1
  simp only [projectionSuffixMap, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows]
  rw [show (1 + ((z - 1) / 2) • P)ᴴ * (1 + ((z - 1) / 2) • P) =
      1 + (((z - 1) / 2) + star ((z - 1) / 2) +
        star ((z - 1) / 2) * ((z - 1) / 2)) • P by
      simpa using projection_gram P hP 1 ((z - 1) / 2)]
  simp only [conjTranspose_smul, hP.isSelfAdjoint.isHermitian.eq, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul,
    hP.isIdempotentElem.eq]
  have hsum : (z - 1) / 2 + star ((z - 1) / 2) +
      star ((z - 1) / 2) * ((z - 1) / 2) +
      ((z - 1) / 2) * star ((z - 1) / 2) = 0 := by
    simp only [star_div₀, star_sub, star_one, star_ofNat]
    linear_combination (1 / 2 : ℂ) * hz
  rw [add_assoc, ← add_smul, hsum, zero_smul, add_zero]

/-- The prefix map coherently records the two projection sectors. -/
def projectionPrefixMap (P : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) ι ℂ :=
  fromRows (1 - P) P

/-- Orthogonality of the two projection sectors normalizes the prefix map. -/
theorem projectionPrefixMap_isIsometry (P : Matrix ι ι ℂ) (hP : IsStarProjection P) :
    (projectionPrefixMap P).IsIsometry := by
  change (projectionPrefixMap P)ᴴ * projectionPrefixMap P = 1
  simp only [projectionPrefixMap, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows, conjTranspose_sub, conjTranspose_one, hP.isSelfAdjoint.isHermitian.eq,
    sub_mul, mul_sub, one_mul, mul_one, hP.isIdempotentElem.eq, sub_self, sub_zero, sub_add_cancel]

/-- The interior map has components `I - P / 2`, `P / 2`, `-P / 2`, `P / 2`. -/
noncomputable def projectionInteriorMap (P : Matrix ι ι ℂ) :
    Matrix ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ι ℂ :=
  fromRows (fromRows (1 - (1 / 2 : ℂ) • P) ((1 / 2 : ℂ) • P))
    (fromRows ((-1 / 2 : ℂ) • P) ((1 / 2 : ℂ) • P))

/-- The interior map is normalized for every orthogonal projection. -/
theorem projectionInteriorMap_isIsometry (P : Matrix ι ι ℂ) (hP : IsStarProjection P) :
    (projectionInteriorMap P).IsIsometry := by
  change (projectionInteriorMap P)ᴴ * projectionInteriorMap P = 1
  simp only [projectionInteriorMap, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
    hP.isSelfAdjoint.isHermitian.eq, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    one_mul, mul_one, hP.isIdempotentElem.eq, star_div₀, star_one, star_neg, star_ofNat]
  module

/-- Left bond vectors `(1,0)` and `(1/2,1/2)`, as columns. -/
noncomputable def projectionLeftFrame : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 1 / 2; 0, 1 / 2]

/-- Right bond vectors `(1,0)` and `(-1,1)`, as columns. -/
def projectionRightFrame : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; 0, 1]

/-- The bilinear kernel that contracts adjacent right and left bond vectors. -/
def projectionMergeKernel : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; 1, 1]

/-- The merging kernel pairs bond columns with the Kronecker delta. -/
theorem projectionMergeKernel_contract_frames :
    projectionRightFrameᵀ * projectionMergeKernel * projectionLeftFrame = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projectionRightFrame, projectionMergeKernel, projectionLeftFrame,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The squared norm of the bond contraction is four. -/
theorem projectionMergeKernel_trace_conjTranspose_mul :
    trace (projectionMergeKernelᴴ * projectionMergeKernel) = 4 := by
  norm_num [projectionMergeKernel, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The inverse-Gram expression for these frames is four, independently of the phase. -/
theorem projectionFrames_trace_inverse_grams :
    trace ((projectionRightFrameᴴ * projectionRightFrame)⁻¹ *
      ((projectionLeftFrameᴴ * projectionLeftFrame)⁻¹)ᵀ) = 4 := by
  norm_num [projectionRightFrame, projectionLeftFrame, Matrix.inv_def, Matrix.det_fin_two,
    Matrix.adjugate_fin_two, Ring.inverse_eq_inv, Matrix.trace_fin_two,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, map_ofNat]

/-- Both bond frames are invertible. -/
theorem projectionFrames_isUnit : IsUnit projectionLeftFrame ∧ IsUnit projectionRightFrame := by
  norm_num [Matrix.isUnit_iff_isUnit_det, projectionLeftFrame, projectionRightFrame,
    Matrix.det_fin_two, isUnit_iff_ne_zero]

end MPUCircuit
