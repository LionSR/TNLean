/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusSemiRegularParentDimension
import TNLean.PEPS.ParentHamiltonian.TorusInvariantClosureMembership

/-!
# Full native semi-regular torus parent ground space

Every commuting native closure satisfies every actual plaquette parent
constraint. Their previously proved linear independence modulo simultaneous
conjugacy gives the full dimension obtained by arbitrary-representation parent
transport. Thus their span exhausts the entire parent kernel, without assuming
any prior closure expansion of a ground vector.

Source: SCP10, arXiv:1001.3807, Theorems 5.7 and 5.9.

**Scope restriction (uniform native semi-regular torus):** Both periods are at
least three in the finite simple-graph model. One uniform semi-regular
representation and one native site tensor repeated at every vertex are used.
Link-dependent representations and smaller periods
remain separate; see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`
and `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.
-/

noncomputable section
open scoped Matrix
namespace TNLean.PEPS
variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "V" => TorusVertex width height
variable {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] {d : ℕ}

/-- The entire native positive plaquette parent kernel is exactly the span of
the actual commuting closure vectors for an arbitrary semi-regular G-injective
physical tensor. No decomposition of a ground vector is assumed.
Source: SCP10, Theorem 5.7, with the stated native-torus scope. -/
theorem IsGInjective.torusParentKernel_eq_commutingClosureSpan_of_isSemiRegular
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (P : (v : V) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker =
      Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
        torusGClosure (width := width) (height := height) U a p.1.1 p.1.2)) := by
  apply (Submodule.eq_of_le_of_finrank_eq
    (span_torusGClosure_commuting_le_torusParentKernel_of_invariant U a ha.invariant P hP) ?_).symm
  rw [ha.finrank_torusParentKernel_of_isSemiRegular hU hSemi P hP,
    range_torusGClosure_commuting_eq_range_torusGClosureClass U a ha.invariant]
  exact ha.finrank_span_torusGClosureClass_commuting_of_isSemiRegular hSemi

/-- Equivalently, all simultaneous canonical plaquette boundary conditions are
exhausted by the actual commuting native closures. -/
theorem IsGInjective.torusParentGroundSpace_eq_commutingClosureSpan_of_isSemiRegular
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    regionParentGroundSpace
      (groupBondTensor (torusNativeIncidentSite (width := width) (height := height) a))
      torusPlaquetteRegion =
      Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
        torusGClosure (width := width) (height := height) U a p.1.1 p.1.2)) := by
  let A := groupBondTensor (torusNativeIncidentSite (width := width) (height := height) a)
  have h := ha.torusParentKernel_eq_commutingClosureSpan_of_isSemiRegular hU hSemi
    (fun v => canonicalRegionParentInteraction A (torusPlaquetteRegion v))
    (fun v => isRegionParentInteraction_canonical A (torusPlaquetteRegion v))
  rwa [ker_regionParentHamiltonian A torusPlaquetteRegion _
    (fun v => isRegionParentInteraction_canonical A (torusPlaquetteRegion v))] at h

end TNLean.PEPS
