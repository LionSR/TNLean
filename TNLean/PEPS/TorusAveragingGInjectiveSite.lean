/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusOperatorString
import TNLean.PEPS.GInjectivePhysicalMap

/-!
# A native G-injective averaging site

The finite-group average supplies a concrete native four-leg G-injective site
for any matrix representation. Numbering its physical output changes no kernel.
Source: SCP10, Definition 5.1(ii) and Section 7.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X]
attribute [local instance] Representation.invertibleFintypeCardComplex

/-- A native four-leg G-injective tensor always exists: take the group average
and enumerate its physical output coordinates. -/
theorem exists_isGInjective_torusSite (U : G →* Matrix X X ℂ) :
    ∃ (p : ℕ) (a : X → X → X → X → Fin p → ℂ),
      IsGInjective (torusLegRep U) (siteMap a) := by
  let := Fintype.ofFinite G
  let ρ := torusLegRep U
  let E := LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin (X × X × X × X)).symm
  let T := E.toLinearMap ∘ₗ ρ.averageMap
  let a : X → X → X → X → Fin (Fintype.card (X × X × X × X)) → ℂ :=
    fun t r b l s => LinearMap.toMatrix' T s (t, r, b, l)
  have hmap : siteMap a = T := by
    apply LinearMap.toMatrix'.injective
    ext s η
    rw [LinearMap.toMatrix'_apply]
    change ((LinearMap.toMatrix' T) *ᵥ Pi.single η 1) s = _
    simp
  have hρ : IsGInjective ρ ρ.averageMap := by
    refine ⟨?_, ?_⟩
    · intro g
      change ρ.averageMap * ρ g = ρ.averageMap
      rw [Representation.averageMap, ← Representation.asAlgebraHom_single_one,
        ← map_mul, GroupAlgebra.mul_average_right]
    · intro x hx hz
      rwa [ρ.averageMap_id x hx] at hz
  refine ⟨_, a, ?_⟩
  rw [hmap]
  exact hρ.comp_equiv E

end TNLean.PEPS
