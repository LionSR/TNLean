/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockGInjectiveIntersection
import TNLean.Algebra.SemiRegularGroupAlgebra

/-!
# The source exterior-arrow convention in matrix coordinates

Reversing an exterior arrow assigns the inverse-transpose representation to
that boundary leg. Applying the outgoing inverse transpose recovers the source
incoming action exactly, and the replacement preserves semi-regularity. This
checks the arrow correspondence for the three-core source theorem independently
of its intersection proof.
-/

noncomputable section
namespace ThreeBlockBoundaryOrientation
variable {G ι : Type*} [Group G] [Fintype ι] [DecidableEq ι]

def contragredient (U : G →* Matrix ι ι ℂ) : G →* Matrix ι ι ℂ where
  toFun g := (U g⁻¹).transpose
  map_one' := by simp
  map_mul' g h := by simp [mul_inv_rev, map_mul, Matrix.transpose_mul]

theorem involutive (U : G →* Matrix ι ι ℂ) :
    contragredient (contragredient U) = U := by
  ext g i j
  simp [contragredient]

theorem tail_recovers_incoming (U : G →* Matrix ι ι ℂ) (g : G) (i j : ι) :
    contragredient U g⁻¹ j i = U g i j := by
  simp [contragredient]

variable [Finite G]

theorem semiRegular (U : G →* Matrix ι ι ℂ)
    (hU : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Representation.IsSemiRegular
      (Matrix.toLinAlgEquiv'.toMonoidHom.comp (contragredient U)) := by
  let e : Matrix ι ι ℂ ≃ₐ[ℂ] Module.End ℂ (ι → ℂ) := Matrix.toLinAlgEquiv'
  have hρ := Representation.linearIndependent_of_isSemiRegular
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp U) hU
  change LinearIndependent ℂ (e.toLinearMap ∘ fun g ↦ U g) at hρ
  have h0 : LinearIndependent ℂ (fun g ↦ U g) :=
    LinearIndependent.of_comp e.toLinearMap hρ
  have h1 := (h0.comp (fun g ↦ g⁻¹) (Equiv.inv G).injective).map'
    (Matrix.transposeLinearEquiv ι ι ℂ ℂ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (Matrix.transposeLinearEquiv ι ι ℂ ℂ).injective)
  have h2 := h1.map' e.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.injective)
  exact Representation.isSemiRegular_of_linearIndependent _ h2

end ThreeBlockBoundaryOrientation

set_option linter.hashCommand false
/--
info: 'ThreeBlockBoundaryOrientation.semiRegular' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ThreeBlockBoundaryOrientation.semiRegular
