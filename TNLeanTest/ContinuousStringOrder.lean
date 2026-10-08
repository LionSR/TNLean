/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ContinuousStringOrder
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Regressions for complex coordinates and continuous physical string order. -/
open scoped Matrix BigOperators Kronecker
open Matrix MPSTensor

namespace ContinuousStringOrderTest
private def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
private def oneLetter : MPSTensor 1 2 := fun _ => Matrix.single 0 0 1

private theorem pauliY_hermitian : pauliY.IsHermitian := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [pauliY, Matrix.conjTranspose_apply]

-- This realignment test is genuinely complex and the commutator is nonzero.
example (a b c e : Fin 2) :
    (rowAdjointGenerator pauliY * (krausRowMatrix oneLetter * (krausRowMatrix oneLetter)ᴴ) -
      (krausRowMatrix oneLetter * (krausRowMatrix oneLetter)ᴴ) * rowAdjointGenerator pauliY)
        (a, b) (c, e) =
    (rowAdjointGenerator pauliY * rowTransferMatrix oneLetter -
      rowTransferMatrix oneLetter * rowAdjointGenerator pauliY) (a, c) (b, e) :=
  krausRowMatrix_gram_commutator_apply oneLetter pauliY pauliY_hermitian a b c e

example :
    (rowAdjointGenerator pauliY * (krausRowMatrix oneLetter * (krausRowMatrix oneLetter)ᴴ) -
      (krausRowMatrix oneLetter * (krausRowMatrix oneLetter)ᴴ) * rowAdjointGenerator pauliY)
        (1, 0) (0, 0) = Complex.I := by
  norm_num [rowAdjointGenerator, krausRowMatrix, oneLetter, pauliY,
    Matrix.mul_apply, Matrix.kronecker_apply, Matrix.conjTranspose_apply,
    Matrix.single_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Matrix.vecMul, dotProduct]

-- At one matrix-unit letter, transposition gives the positive sign.
example : (∑ j : Fin 2 × Fin 2,
    (rowAdjointGenerator pauliY)ᵀ (0, 0) j • Matrix.single j.1 j.2 (1 : ℂ)) =
    pauliY * Matrix.single 0 0 1 - Matrix.single 0 0 1 * pauliY := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rowAdjointGenerator, pauliY, Matrix.mul_apply, Matrix.kronecker_apply,
      Matrix.transpose_apply, Matrix.single_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ,
    Matrix.vecMul, dotProduct]

-- Omitting that transpose really is wrong for Pauli Y.
example : (∑ j : Fin 2 × Fin 2,
    (rowAdjointGenerator pauliY) (0, 0) j • Matrix.single j.1 j.2 (1 : ℂ)) ≠
    pauliY * Matrix.single 0 0 1 - Matrix.single 0 0 1 * pauliY := by
  intro h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
  norm_num [rowAdjointGenerator, pauliY, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.single_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Matrix.vecMul, dotProduct] at h10
  have him := congrArg Complex.im h10
  norm_num at him

end ContinuousStringOrderTest

/--
info: 'MPSTensor.commute_rowTransferMatrix_iff_commute_krausGram' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.commute_rowTransferMatrix_iff_commute_krausGram

/--
info: 'MPSTensor.infinitesimal_physical_covariance_of_intertwiner' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.infinitesimal_physical_covariance_of_intertwiner

/--
info: 'MPSTensor.condC1_hermitianUnitaryPath_of_intertwiner' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.condC1_hermitianUnitaryPath_of_intertwiner

/--
info: 'MPSTensor.exists_hermitian_physical_generator' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.exists_hermitian_physical_generator

/--
info: 'MPSTensor.eq_scalar_of_scalar_commutator_action' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.eq_scalar_of_scalar_commutator_action

/--
info: 'MPSTensor.physicalStringOrderParam_identity_tendsto' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.physicalStringOrderParam_identity_tendsto

/--
info: 'MPSTensor.eventually_trace_virtualPath_ne_zero' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.eventually_trace_virtualPath_ne_zero

/--
info: 'MPSTensor.pureCanonical_continuous_generator_identity_endpoints' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_continuous_generator_identity_endpoints

/--
info: 'MPSTensor.hasPhysicalStringOrder_of_continuous_generator' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.hasPhysicalStringOrder_of_continuous_generator
