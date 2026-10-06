/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CommutingMatrixProjectionProduct

/-! Regression contracts for empty lists, repeated constraints and axiom dependencies. -/

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- No constraint is imposed by an empty product.
example (P : Unit → Matrix ι ι ℂ) (v : ι → ℂ) :
    (([] : List Unit).map P).prod *ᵥ v = v := by
  simp

-- Repeating a projector does not strengthen the fixed-vector condition.
example (A : Matrix ι ι ℂ) (hA : IsStarProjection A) (v : ι → ℂ) :
    ([(), (), ()].map (fun _ : Unit => A)).prod *ᵥ v = v ↔ A *ᵥ v = v := by
  simpa using Matrix.list_prod_mulVec_eq_self_iff
    (fun _ : Unit => A) (fun _ => hA) (fun _ _ => Commute.refl A) [(), (), ()] v

set_option linter.hashCommand false

/--
info: 'Matrix.isStarProjection_list_prod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.isStarProjection_list_prod

/--
info: 'Matrix.list_prod_mulVec_eq_self_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.list_prod_mulVec_eq_self_iff
