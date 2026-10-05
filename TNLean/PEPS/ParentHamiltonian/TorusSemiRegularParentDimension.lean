/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.OrientedSemiRegularGInjectiveParentTransport
import TNLean.PEPS.ParentHamiltonian.TorusRegularParentGroundSpace
import TNLean.PEPS.TorusOrientedIncidentGInjectivity
import TNLean.PEPS.TorusAveragingGInjectiveSite

/-!
# Full native semi-regular torus parent dimension

Native top/left incoming and right/down outgoing legs are identified with the
actual graph's explicit edge orientation. Arbitrary positive multiplicities
and arbitrary G-injective physical tensors then reduce to the regular native
parent theorem. Thus the complete parent kernel has the source's commuting
pair class count, without assuming a closure expansion or a representation
block decomposition.

Source: SCP10, arXiv:1001.3807, Theorem 5.9.

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
variable {G X : Type*} [Group G] [Finite G]
variable [Fintype X] [DecidableEq X] {d : ℕ}

/-- The actual native plaquette parent space of an arbitrary semi-regular
G-injective tensor has the regular commuting-pair class dimension. -/
theorem IsGInjective.finrank_torusParentGroundSpace_of_isSemiRegular
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U)) :
    Module.finrank ℂ (regionParentGroundSpace
      (groupBondTensor (torusNativeIncidentSite (width := width) (height := height) a))
      torusPlaquetteRegion) = Nat.card (CommutingPairConjugacyClass G) := by
  classical
  let := Fintype.ofFinite G
  have hv : ∀ v : V, ∃ i, v ∈ torusPlaquetteRegion i :=
    fun v => ⟨v, mem_torusPlaquetteRegion_self v⟩
  have he := exists_torusPlaquetteRegion_contains_edge (width := width) (height := height)
  have hdim := finrank_regionParentGroundSpace_orientedSemiRegularGInjective_eq
    U torusNativeEdgeFlip hU hSemi (torusNativeIncidentSite a)
    ha.isGInjective_torusNativeIncidentTensor 4 card_torusIncidentEdge
    torusPlaquetteRegion hv he
  obtain ⟨p, b, hb⟩ := exists_isGInjective_torusSite (leftRegularMatrix G)
  obtain ⟨E⟩ := nonempty_gInjectiveOrientedCanonicalParentEquiv
    (leftRegularMatrix G) torusNativeEdgeFlip (torusNativeIncidentSite b)
    hb.isGInjective_torusNativeIncidentTensor
    (countedIncidentEnumeration G 4 card_torusIncidentEdge) torusPlaquetteRegion hv
  let B := groupBondTensor (torusIncidentSite (width := width) (height := height) b)
  have hreg := hb.finrank_torusParentKernel
    (fun v : V => canonicalRegionParentInteraction B (torusPlaquetteRegion v))
    (fun v => isRegionParentInteraction_canonical B (torusPlaquetteRegion v))
  rw [ker_regionParentHamiltonian B torusPlaquetteRegion _
    (fun v => isRegionParentInteraction_canonical B (torusPlaquetteRegion v))] at hreg
  exact hdim.trans (E.finrank_eq.symm.trans hreg)

/-- The entire positive native plaquette Hamiltonian kernel has exactly the
number of simultaneous conjugacy classes of commuting pairs, for arbitrary
unitary semi-regular virtual representations and G-injective physical tensors. -/
theorem IsGInjective.finrank_torusParentKernel_of_isSemiRegular
    {U : G →* Matrix X X ℂ} {a : X → X → X → X → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep U) (siteMap a))
    (hU : ∀ g, U g ∈ Matrix.unitaryGroup X ℂ)
    (hSemi : Representation.IsSemiRegular (Matrix.toLinAlgEquiv'.toMonoidHom.comp U))
    (P : (v : V) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusNativeIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker =
      Nat.card (CommutingPairConjugacyClass G) := by
  rw [ker_regionParentHamiltonian _ torusPlaquetteRegion P hP]
  exact ha.finrank_torusParentGroundSpace_of_isSemiRegular hU hSemi

end TNLean.PEPS
