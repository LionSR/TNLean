/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusNonuniformParentSeamCuts
import TNLean.PEPS.RegularMatrixEquiv
import TNLean.Algebra.SemiRegularGroupAlgebra

/-! # Nonabelian microscopic parent-to-seam regression -/

noncomputable section
open TNLean.PEPS TNLean.PEPS.DependentBondNetwork

namespace NonabelianNativeParent
local instance : Fact (2 < 3) := ⟨by decide⟩
local instance : Fact (1 < 3) := ⟨by decide⟩
abbrev V := TorusVertex 3 3
abbrev Γ := torusGraph 3 3
abbrev G := Equiv.Perm (Fin 3)
private abbrev N (_ : Edge Γ) := Fintype.card G
private abbrev D (_ : Edge Γ) := Fin (Fintype.card G)

private def reindex := Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin G)
private def U (_ : Edge Γ) : G →* Matrix (Fin (Fintype.card G)) (Fin (Fintype.card G)) ℂ :=
  reindex.toMonoidHom.comp (leftRegularMatrix G)

private theorem semiRegular (e : Edge Γ) :
    Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)) := by
  let T : Module.End ℂ (G → ℂ) ≃ₐ[ℂ] Module.End ℂ (Fin (Fintype.card G) → ℂ) :=
    Matrix.toLinAlgEquiv'.symm.trans (reindex.trans Matrix.toLinAlgEquiv')
  have hi := Representation.linearIndependent_of_isSemiRegular _
    (isSemiRegular_leftRegularMatrix (G := G))
  have ht := hi.map' T.toLinearMap (LinearMap.ker_eq_bot.mpr T.injective)
  apply Representation.isSemiRegular_of_linearIndependent
  convert ht using 1
  funext g
  simp [T, U, Function.comp_def]

private abbrev Phys (v : V) := LocalConfig graphEdgeTail graphEdgeHead D v
private def A (v : V) : LocalConfig graphEdgeTail graphEdgeHead D v → Phys v → ℂ :=
  DependentBondNetwork.averagingSite graphEdgeTail graphEdgeHead D U v
private abbrev B := graphPhysicalPaddingTensor N A
private def H (v : V) := canonicalRegionParentInteraction B (torusPlaquetteRegion v)

/-- Every physical kernel vector of the actual nonabelian canonical parent
has the full native seam-boundary family. -/
theorem every_parent_vector
    {Ψ : (V → Fin (physicalPaddingDimension (Phys := Phys))) → ℂ}
    (hΨ : Ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker) :
    ∃ ψ : ((v : V) → Phys v) → ℂ,
      dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) ψ = Ψ ∧
      ∀ (c r : ZMod 3), ∃ M : CutConfig (torusGraphSeamCut c r) D → ℂ,
        ∀ σ, cutCoeff graphEdgeTail graphEdgeHead D A (torusGraphSeamCut c r) M σ = ψ σ :=
  exists_nonuniform_seamBoundaries_of_mem_torusPlaquetteParentKernel N U semiRegular A
    (isGInjective_averagingSite graphEdgeTail graphEdgeHead D U) H
    (fun v ↦ isRegionParentInteraction_canonical B (torusPlaquetteRegion v)) hΨ

example : ¬ Commute (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (1 : Fin 3) 2) := by
  intro h
  have hh := congrArg (fun p : G ↦ p 0) h.eq
  norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hh

end NonabelianNativeParent

set_option linter.hashCommand false
/--
info: 'NonabelianNativeParent.every_parent_vector' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NonabelianNativeParent.every_parent_vector
