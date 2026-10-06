/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.GroupAction

/-!
# Regression tests for group actions determined by nonnegative multiplicities

The natural action of the noncommutative group of permutations of three points is recovered
from its multiplicity matrices. The two orders of adjacent transpositions have different
images, testing the composition convention. The final checks test uniqueness as an action.
-/

open MPOTensor

namespace GLM23GroupActionChecks

private def multiplicity (g : Equiv.Perm (Fin 3)) (x y : Fin 3) : ℕ :=
  if y = g x then 1 else 0

private theorem nim : IsNIMRep
    (fun g h k : Equiv.Perm (Fin 3) ↦ if k = g * h then 1 else 0) multiplicity := by
  intro g h x y
  simp only [multiplicity, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

private theorem unit : ∀ x y, multiplicity 1 x y = if y = x then 1 else 0 := by
  intro x y
  rfl

example (g : Equiv.Perm (Fin 3)) : nim.groupPerm unit g = g := by
  apply Equiv.ext
  exact congrFun (nim.groupPerm_eq_of_coefficients unit g g (fun _ _ ↦ rfl))

example : nim.groupPerm unit (Equiv.swap 0 1 * Equiv.swap 1 2) 0 = 1 := by
  apply (nim.groupPerm_apply_eq_iff unit _ 0 1).2
  decide +kernel

example : nim.groupPerm unit (Equiv.swap 1 2 * Equiv.swap 0 1) 0 = 2 := by
  apply (nim.groupPerm_apply_eq_iff unit _ 0 2).2
  decide +kernel

example : nim.toMulAction unit = Equiv.Perm.applyMulAction (Fin 3) :=
  nim.toMulAction_unique unit _ (fun _ _ _ ↦ rfl)

example : ∃! μ : MulAction (Equiv.Perm (Fin 3)) (Fin 3), letI := μ
    ∀ g x y, multiplicity g x y = if y = g • x then 1 else 0 :=
  nim.existsUnique_mulAction unit

end GLM23GroupActionChecks
