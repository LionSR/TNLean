/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.GHZ
import TNLean.MPS.Preparation.SupportedPolar

/-!
# A virtual rotation need not preserve coordinate support

The GHZ flags `|0⟩⟨0|`, `|1⟩⟨1|`, rotated on their left virtual leg by the rational unitary
`R = [[3/5,-4/5],[4/5,3/5]]`, give a coisometric physical matrix whose virtual range is not
any coordinate subspace. In particular no set of bond pairs makes this tensor injective on
that set. Rank bounds and an isometric physical range therefore do not supply the coordinate
support hypothesis of the existing supported polar-tree construction.

This is an obstruction to that particular reuse of the tree theorem, not to preparation by
a tree with general, position-dependent virtual subspaces. For the inhomogeneous remark
after eq. (19) of arXiv:2307.01696 see
`docs/paper-gaps/mswc24_inhomogeneous_long_range.tex`.
-/

open Matrix

namespace MPSTensor

/-- A nontrivial rational unitary on the two-dimensional virtual space. -/
def flagRotation : Matrix (Fin 2) (Fin 2) ℂ := !![3 / 5, -4 / 5; 4 / 5, 3 / 5]

/-- The rational virtual rotation preserves inner products. -/
theorem conjTranspose_flagRotation_mul : flagRotationᴴ * flagRotation = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flagRotation, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply]

/-- The two GHZ flags after rotating their left virtual leg. -/
def rotatedGHZFlag : MPSTensor 2 2 := fun i => flagRotation * ghzTensor i

/-- The physical matrix has two orthonormal rows, so neither physical dimension is lost. -/
theorem physicalMatrix_rotatedGHZFlag_mul_conjTranspose :
    physicalMatrix rotatedGHZFlag * (physicalMatrix rotatedGHZFlag)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [physicalMatrix, rotatedGHZFlag, flagRotation, ghzTensor, Matrix.mul_apply,
      Fin.sum_univ_two, Fintype.sum_prod_type, conjTranspose_apply]

private def flagConstraint : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  (3 : ℂ) • Matrix.entryLinearMap ℂ ℂ 1 0 -
    (4 : ℂ) • Matrix.entryLinearMap ℂ ℂ 0 0

/-- No coordinate set is the injective virtual support of the rotated flags. This is a
nondegenerate counterexample to replacing arbitrary virtual support by coordinate support. -/
theorem not_exists_isInjectiveOn_rotatedGHZFlag :
    ¬∃ S : Set (Fin 2 × Fin 2), IsInjectiveOn rotatedGHZFlag S := by
  rintro ⟨S, hS⟩
  have hp : ((0 : Fin 2), (0 : Fin 2)) ∈ S := by
    by_contra hp
    have hz := hS.1 0 (0, 0) hp
    norm_num [rotatedGHZFlag, flagRotation, ghzTensor, Matrix.mul_apply,
      Fin.sum_univ_two] at hz
  have hker : Submodule.span ℂ (Set.range rotatedGHZFlag) ≤ LinearMap.ker flagConstraint := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change 3 * (rotatedGHZFlag i) 1 0 - 4 * (rotatedGHZFlag i) 0 0 = 0
    fin_cases i <;>
      norm_num [rotatedGHZFlag, flagRotation, ghzTensor, Matrix.mul_apply, Fin.sum_univ_two]
  have hsingle := hker (hS.2 (0, 0) hp)
  change 3 * (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) 1 0 -
    4 * (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) 0 0 = 0 at hsingle
  norm_num [Matrix.single_apply] at hsingle

end MPSTensor
