/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusNonuniformParentSeamCuts
import TNLean.Algebra.SemiRegularGroupAlgebra

/-!
# Nonuniform physical parent-to-seam regressions

The actual microscopic parent on a three-by-three native torus is built from
nonsurjective scaled coordinate inclusions. One bond has dimension two, the
others dimension one; physical alphabets are independently enlarged by one
unused coordinate. No local-image condition is added to its ambient kernel.
-/

noncomputable section
open scoped BigOperators
open TNLean.PEPS TNLean.PEPS.DependentBondNetwork

namespace NonuniformNativeParent
local instance : Fact (2 < 3) := ⟨by decide⟩
local instance : Fact (1 < 3) := ⟨by decide⟩
abbrev V := TorusVertex 3 3
abbrev Γ := torusGraph 3 3

private def N (e : Edge Γ) : ℕ := if e = torusRightEdge (0 : V) then 2 else 1
private abbrev D (e : Edge Γ) := Fin (N e)
private instance (e : Edge Γ) : Nonempty (D e) := by
  dsimp [D, N]
  split_ifs <;> infer_instance
private abbrev Phys (v : V) := Option (LocalConfig graphEdgeTail graphEdgeHead D v)

private def U (e : Edge Γ) : Unit →* Matrix (D e) (D e) ℂ := 1
private def A (v : V) (η : LocalConfig graphEdgeTail graphEdgeHead D v) (s : Phys v) : ℂ :=
  if s = some η then 2 else 0

private theorem semiRegular (e : Edge Γ) :
    Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp (U e)) := by
  rw [Representation.isSemiRegular_iff_linearIndependent, linearIndependent_unique_iff]
  have hg : (default : Unit) = 1 := rfl
  rw [hg, map_one]
  exact one_ne_zero

private theorem site_gInjective (v : V) :
    IsGInjective (incidentRepresentation graphEdgeTail graphEdgeHead D U v)
      (localSiteMap graphEdgeTail graphEdgeHead D A v) := by
  have hρ : incidentRepresentation graphEdgeTail graphEdgeHead D U v =
      Representation.trivial ℂ Unit (LocalConfig graphEdgeTail graphEdgeHead D v → ℂ) := by
    apply MonoidHom.ext
    intro g
    have hg : g = 1 := Subsingleton.elim _ _
    rw [hg, map_one, map_one]
  rw [hρ, isGInjective_trivial_iff]
  intro x y h
  funext η
  have hs := congrFun h (some η)
  change (∑ ζ, A v ζ (some η) * x ζ) = ∑ ζ, A v ζ (some η) * y ζ at hs
  simpa [A] using hs

private abbrev B := graphPhysicalPaddingTensor N A
private def H (v : V) := canonicalRegionParentInteraction B (torusPlaquetteRegion v)

/-- The entire ambient positive kernel has actual seam witnesses on the
independent physical spaces, with no added support condition. -/
theorem every_parent_vector
    {Ψ : (V → Fin (physicalPaddingDimension (Phys := Phys))) → ℂ}
    (hΨ : Ψ ∈ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion H)).ker) :
    ∃ ψ : ((v : V) → Phys v) → ℂ,
      dependentPhysicalProductFamilyMap (physicalPaddingMatrix (Phys := Phys)) ψ = Ψ ∧
      ∀ (c r : ZMod 3), ∃ M : CutConfig (torusGraphSeamCut c r) D → ℂ,
        ∀ σ, cutCoeff graphEdgeTail graphEdgeHead D A (torusGraphSeamCut c r) M σ = ψ σ :=
  exists_nonuniform_seamBoundaries_of_mem_torusPlaquetteParentKernel N U semiRegular A
    site_gInjective H (fun v ↦ isRegionParentInteraction_canonical B (torusPlaquetteRegion v)) hΨ

example : Fintype.card (D (torusRightEdge (0 : V))) = 2 := by simp [D, N]
example : Fintype.card (D (torusUpEdge (0 : V))) = 1 := by
  have hne : torusUpEdge (0 : V) ≠ torusRightEdge (0 : V) := by
    change torusEdgeEquiv (Sum.inr (0 : V)) ≠ torusEdgeEquiv (Sum.inl (0 : V))
    exact fun h ↦ Sum.inr_ne_inl (torusEdgeEquiv.injective h)
  simp [D, N, hne]

-- Two endpoints of the doubled bond have three physical coordinates; other sites have two.
example : Fintype.card (Phys (0 : V)) = 3 := by decide
example : Fintype.card (Phys (1, 1)) = 2 := by decide

-- The two selected horizontal seams really differ, as do the two vertical seams.
example : torusRightEdge (2, 0) ∈ torusGraphSeamCut (0 : ZMod 3) (0 : ZMod 3) := by
  rw [torusRightEdge_mem_graphSeamCut]; decide
example : torusRightEdge (2, 0) ∉ torusGraphSeamCut (1 : ZMod 3) (0 : ZMod 3) := by
  rw [torusRightEdge_mem_graphSeamCut]; decide
example : torusUpEdge (0, 2) ∈ torusGraphSeamCut (0 : ZMod 3) (0 : ZMod 3) := by
  rw [torusUpEdge_mem_graphSeamCut]; decide
example : torusUpEdge (0, 2) ∉ torusGraphSeamCut (0 : ZMod 3) (1 : ZMod 3) := by
  rw [torusUpEdge_mem_graphSeamCut]; decide

end NonuniformNativeParent

set_option linter.hashCommand false
/--
info: 'NonuniformNativeParent.every_parent_vector' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NonuniformNativeParent.every_parent_vector

/--
info: 'TNLean.PEPS.exists_nonuniform_seamBoundaries_of_mem_torusPlaquetteParentKernel'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_nonuniform_seamBoundaries_of_mem_torusPlaquetteParentKernel
