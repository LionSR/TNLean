/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusRegularParentCoordinates
import TNLean.PEPS.ParentHamiltonian.TorusParentFlatness
import TNLean.PEPS.TorusFlatConnectionGauge

/-!
# Every native regular torus parent ground vector is a sum of commuting closures

Apply local regular inverses to an arbitrary physical parent ground vector.
The exposed vector is invariant under vertex-left and shared-edge-right
translations and is supported on flat plaquette quotients. Its finite orbit
expansion therefore contains only flat inserted canonical projector states.
Applying the original site tensors recovers the physical vector. Every flat
insertion is gauge equivalent to two commuting seams, so each term in this
expansion is a commuting native torus closure.

This proves the global spanning direction of SCP10, arXiv:1001.3807,
Theorems 5.5 and 5.7 for the regular representation on native simple tori with both
periods at least three. No prior closure-span membership is assumed. The
extension to arbitrary semi-regular virtual representations is separate.

**Scope restriction (regular native torus):** The virtual representation is regular
and both periods are at least three. The semi-regular parent-kernel and
smaller-period statements remain separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
local notation "Γₜ" => torusGraph width height

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- Every flat inserted regular torus PEPS is an actual commuting closure.
Source: SCP10, Theorem 5.5 and closure-string deformation. -/
theorem IsGInjective.stateCoeff_mem_commutingClosureSpan_of_flat
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (u : Edge Γₜ → G)
    (hu : ∀ v : X, regularWalkHolonomy u (torusPlaquetteWalk v) = 1) :
    stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) ∈
      Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
        torusGClosure (width := width) (height := height)
          (leftRegularMatrix G) a p.1.1 p.1.2)) := by
  have hflat : IsTorusFlat (torusNativeRightTransport u) (torusNativeUpTransport u) :=
    fun v => (torusPlaquetteHolonomy_eq_one_iff_squareTransport u v).mp (hu v)
  obtain ⟨g, h, hgh, hstate⟩ := exists_sameState_torusClosure_of_isTorusFlat
    (torusIncidentSite a)
    (fun k v η s => (ha.isGInjective_torusIncidentSite v).regularSiteMap_translation k η s)
    u hflat
  apply Submodule.subset_span
  refine ⟨⟨(g, h), hgh⟩, ?_⟩
  funext σ
  change torusGClosure (leftRegularMatrix G) a g h σ = _
  rw [torusGClosure_eq_stateCoeff_twisted]
  exact (hstate σ).symm

/-- The full native plaquette parent kernel is contained in the span of
commuting native closures. Unlike a kernel-intersection statement, this
conclusion applies to every physical kernel vector, without an assumed
inserted-bond or closure-span representation.
Source: SCP10, Theorem 5.7, regular representation and periods at least three. -/
theorem IsGInjective.torusParentKernel_le_commutingClosureSpan
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker ≤
      Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
        torusGClosure (width := width) (height := height)
          (leftRegularMatrix G) a p.1.1 p.1.2)) := by
  classical
  intro Ψ hΨ
  have hlocal : ∀ v, regionLocalTerm (torusPlaquetteRegion v) (P v) *ᵥ Ψ = 0 :=
    (regionParentHamiltonian_mulVec_eq_zero_iff torusPlaquetteRegion P
      (fun v => (hP v).1) Ψ).mp hΨ
  obtain ⟨F, hF, hrec, hleft, hright, hsupport⟩ :=
    ha.exists_torusParentCoordinates P hP Ψ hlocal
  let f : RegularHalfEdgeConfig Γₜ G → ℂ := fun α =>
    globalDependentPhysicalMap F Ψ (fun w => α w.1)
  let Flat (u : Edge Γₜ → G) : Prop :=
    ∀ v : X, regularWalkHolonomy u (torusPlaquetteWalk v) = 1
  let : DecidablePred Flat := fun u => Classical.propDecidable (Flat u)
  have hexp := eq_sum_supported_regularProjectorClosedState_of_invariant
    Flat f hleft hright hsupport
  have hfull : globalDependentPhysicalMap F Ψ =
      ∑ u : {u : Edge Γₜ → G // Flat u},
        f (regularHalfEdgeOfOperators u.1) •
          (fun α => regularProjectorClosedState u.1 (fullRegionHalfEdgeConfigEquiv α)) := by
    funext α
    have h := congrFun hexp (fullRegionHalfEdgeConfigEquiv α)
    simpa only [Finset.sum_apply, Pi.smul_apply, f, fullRegionHalfEdgeConfigEquiv,
      Equiv.coe_fn_mk] using h
  rw [← hrec, hfull, map_sum]
  apply Submodule.sum_mem
  intro u _
  rw [map_smul, globalRegularTensorMap_regularProjectorClosedState
    (torusIncidentSite a) (fun v => ha.isGInjective_torusIncidentSite v)]
  exact Submodule.smul_mem _ _
    (ha.stateCoeff_mem_commutingClosureSpan_of_flat u.1 u.2)

end TNLean.PEPS
