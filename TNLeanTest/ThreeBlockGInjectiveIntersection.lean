/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.ThreeBlockGInjectiveIntersection
import TNLean.Algebra.SemiRegularGroupAlgebra

/-!
# Three-core G-injective intersection regression

The virtual dimensions are 1 through 10. Physical alphabets are independent
coordinate extensions of the three four-leg spaces, and local tensors multiply
the coordinate inclusion by two. For the trivial group all ten bond actions are
semi-regular, while nine are nonregular. The test invokes the actual three-core
intersection, retaining unrestricted omitted physical factors and eight virtual
boundary legs.
-/

open scoped BigOperators
open TNLean.PEPS TNLean.PEPS.DependentBondNetwork
open TNLean.PEPS.ThreeBlockDependent

namespace IndependentOpenDimensions

abbrev D (e : Bond) := Fin (e.val + 1)
abbrev Phys (v : Core) := Option (ThreeBlockDependent.LocalConfig D v.1)

noncomputable def U (e : Bond) : PUnit.{1} →* Matrix (D e) (D e) ℂ := 1

noncomputable def A (v : Core) (η : ThreeBlockDependent.LocalConfig D v.1) (s : Phys v) : ℂ :=
  if s = some η then 2 else 0

private theorem semiRegular (e : Bond) :
    Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)) := by
  rw [Representation.isSemiRegular_iff_linearIndependent, linearIndependent_unique_iff]
  have hdefault : (default : PUnit.{1}) = 1 := rfl
  rw [hdefault, map_one]
  exact one_ne_zero

private theorem incidentRepresentation_trivial (v : Core) :
    incidentRepresentation tail head D U v.1 = Representation.trivial ℂ PUnit.{1}
      (ThreeBlockDependent.LocalConfig D v.1 → ℂ) := by
  apply MonoidHom.ext
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  rw [hg, map_one, map_one]

private theorem site_injective (v : Core) :
    Function.Injective (Matrix.mulVecLin (fun s η ↦ A v η s)) := by
  classical
  intro x y h
  funext η
  have hη := congrFun h (some η)
  change (∑ ζ, A v ζ (some η) * x ζ) = ∑ ζ, A v ζ (some η) * y ζ at hη
  simpa [A] using hη

example :
    coreLiftedCutSpace D (extendedTensor D A) leftVertices (by decide) leftCut ⊓
        coreLiftedCutSpace D (extendedTensor D A) rightVertices (by decide) rightCut =
      openBoundarySpace D (extendedTensor D A) := by
  apply coreLiftedCutSpace_inf_eq_openBoundarySpace D U semiRegular A
  intro v
  rw [incidentRepresentation_trivial, isGInjective_trivial_iff]
  exact site_injective v

example :
    regionalBoundarySpace D (extendedTensor D A) leftVertices (by decide) leftCut (by decide) ⊓
        regionalBoundarySpace D (extendedTensor D A)
          rightVertices (by decide) rightCut (by decide) =
      openBoundarySpace D (extendedTensor D A) := by
  apply regionalBoundarySpace_inf_eq_openBoundarySpace D U semiRegular A
  intro v
  rw [incidentRepresentation_trivial, isGInjective_trivial_iff]
  exact site_injective v

example : Fintype.card (RegionBoundaryEndpoint leftVertices leftCut) = 6 := by decide
example : Fintype.card (RegionBoundaryEndpoint rightVertices rightCut) = 6 := by decide

example : Fintype.card {e : Bond // e ∈ exteriorBonds} = 8 := by decide
example : Fintype.card Core = 3 := by decide

end IndependentOpenDimensions

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.ThreeBlockDependent.coreLiftedCutSpace_inf_eq_openBoundarySpace'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ThreeBlockDependent.coreLiftedCutSpace_inf_eq_openBoundarySpace

/--
info: 'TNLean.PEPS.ThreeBlockDependent.regionalBoundarySpace_inf_eq_openBoundarySpace'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.ThreeBlockDependent.regionalBoundarySpace_inf_eq_openBoundarySpace
