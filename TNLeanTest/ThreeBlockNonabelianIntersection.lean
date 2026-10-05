/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockGInjectiveIntersection
import TNLean.PEPS.RegularMatrixEquiv

/-!
# Nonabelian three-block open-region intersection

The full source-scope regional theorem is instantiated for the permutation
group on three letters and its regular representation. The final example
checks that the group has noncommuting elements, so no abelian specialization
can discharge this regression.
-/

noncomputable section
open TNLean.PEPS TNLean.PEPS.DependentBondNetwork
open TNLean.PEPS.ThreeBlockDependent

namespace NonabelianOpenIntersection
abbrev G := Equiv.Perm (Fin 3)
abbrev D (_ : Bond) := G
abbrev Phys (v : Core) := ThreeBlockDependent.LocalConfig D v.1

def U (_ : Bond) : G →* Matrix G G ℂ := leftRegularMatrix G

def A (v : Core) : ThreeBlockDependent.LocalConfig D v.1 → Phys v → ℂ :=
  averagingSite tail head D U v.1

theorem intersection :
    regionalBoundarySpace D (extendedTensor D A) leftVertices (by decide) leftCut (by decide) ⊓
        regionalBoundarySpace D (extendedTensor D A)
          rightVertices (by decide) rightCut (by decide) =
      openBoundarySpace D (extendedTensor D A) := by
  apply regionalBoundarySpace_inf_eq_openBoundarySpace D U
    (fun _ ↦ isSemiRegular_leftRegularMatrix) A
  intro v
  exact isGInjective_averagingSite tail head D U v.1

example : ¬ Commute (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2) := by
  intro h
  have hh := congrArg (fun p : Equiv.Perm (Fin 3) ↦ p 0) h.eq
  norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hh

end NonabelianOpenIntersection

set_option linter.hashCommand false
/--
info: 'NonabelianOpenIntersection.intersection' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NonabelianOpenIntersection.intersection
