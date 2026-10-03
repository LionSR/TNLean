/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionFlatness
import TNLean.PEPS.TorusPlaquetteFluxMeasurement
import TNLean.PEPS.TorusIncidentGInjectivity
import TNLean.PEPS.TorusParallelSection

/-!
# Plaquette flatness forced by regular torus parent constraints

An original local parent term excludes every nonzero inserted regular
G-injective torus state whose plaquette holonomy is nontrivial. Thus the
regional parent constraints force flatness of any inserted-bond description
of a nonzero state. This proves a necessary local implication in the torus
closure argument; it does not represent every parent-kernel vector by an
inserted-bond state. No G-isometry or flux measurement assumption is used.

**Scope restriction (regular native torus flatness):** Both periods are at
least three, and the virtual representation is regular. These restrictions
are recorded in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
Source: SCP10, arXiv:1001.3807, proof of Theorem 5.5, lines 1440–1514,
and the fluxon string discussion, lines 2181–2197.
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

/-- A local parent constraint on the four plaquette sites forces identity
holonomy in every nonzero inserted regular G-injective torus state. Source:
SCP10, converse closure constraints in Theorem 5.5, lines 1440–1514. -/
theorem IsGInjective.torusPlaquetteHolonomy_eq_one_of_parent_annihilates
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : X) (u : Edge Γₜ → G)
    (Q : Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hQ : IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) Q)
    (hne : stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) ≠ 0)
    (hground : regionLocalTerm (torusPlaquetteRegion v) Q *ᵥ
      stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) = 0) :
    regularWalkHolonomy u (torusPlaquetteWalk v) = 1 := by
  classical
  let R := torusPlaquetteRegion v
  have hsupport : ∀ x ∈ (torusPlaquetteWalk v).support, x ∈ (R : Set X) := by
    intro x hx
    exact List.mem_toFinset.mpr hx
  have hR : ((Γₜ).induce (R : Set X)).Connected := by
    have heq : (R : Set X) = {x | x ∈ (torusPlaquetteWalk v).support} := by
      ext x
      simp [R, torusPlaquetteRegion]
    rw [heq]
    exact (torusPlaquetteWalk v).connected_induce_support
  let o : {x : X // x ∈ R} := ⟨v, hsupport _ (torusPlaquetteWalk v).start_mem_support⟩
  let p : ((Γₜ).induce (R : Set X)).Walk o o :=
    (torusPlaquetteWalk v).induce (R : Set X) hsupport
  have h := regularWalkHolonomy_eq_one_of_regionParent_annihilates_twistedState
    (torusIncidentSite a) (fun w => ha.isGInjective_torusIncidentSite w)
    R hR u o p Q hQ hne hground
  dsimp only [p] at h
  rw [regularWalkHolonomy_inducedWalk, SimpleGraph.Walk.map_induce] at h
  exact h

/-- A nonzero one-bond flux state with nonidentity flux cannot satisfy the
original plaquette parent constraint. Source: SCP10, fluxon strings,
lines 2181–2197; auxiliary regular G-injective parent exclusion. -/
theorem IsGInjective.regionParent_not_annihilates_torusPlaquetteFlux
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (v : X) (g : G) (hg : g ≠ 1)
    (Q : Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hQ : IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) Q)
    (hne : stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a)
      (torusPlaquetteFluxInsertion v g))) ≠ 0) :
    regionLocalTerm (torusPlaquetteRegion v) Q *ᵥ
      stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a)
        (torusPlaquetteFluxInsertion v g))) ≠ 0 := by
  intro hzero
  apply hg
  simpa only [regularWalkHolonomy_torusPlaquetteFluxInsertion] using
    ha.torusPlaquetteHolonomy_eq_one_of_parent_annihilates
      v (torusPlaquetteFluxInsertion v g) Q hQ hne hzero

/-- The complete plaquette parent forces identity holonomy around every
native square in any nonzero inserted regular G-injective PEPS. Source:
SCP10, necessary closure constraints in Theorem 5.5, lines 1440–1514. -/
theorem IsGInjective.torusPlaquetteHolonomy_eq_one_of_parentHamiltonian_annihilates
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (u : Edge Γₜ → G)
    (Q : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hQ : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (Q v))
    (hne : stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) ≠ 0)
    (hground : regionParentHamiltonian torusPlaquetteRegion Q *ᵥ
      stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) = 0) :
    ∀ v : X, regularWalkHolonomy u (torusPlaquetteWalk v) = 1 := by
  intro v
  exact ha.torusPlaquetteHolonomy_eq_one_of_parent_annihilates v u (Q v) (hQ v) hne
    ((regionParentHamiltonian_mulVec_eq_zero_iff torusPlaquetteRegion Q
      (fun w => (hQ w).1) _).mp hground v)

omit [Fintype G] [DecidableEq G] in
/-- Identity plaquette holonomy is precisely equality of the two elementary
square transports in the native graph. Source: SCP10, string deformation,
lines 1622–1647, auxiliary transport form of the local closure constraint. -/
theorem torusPlaquetteHolonomy_eq_one_iff_squareTransport (u : Edge Γₜ → G) (v : X) :
    regularWalkHolonomy u (torusPlaquetteWalk v) = 1 ↔
      regularDirectedTransport u (torusGraph_adj_up (v.1 + 1) v.2) *
        regularDirectedTransport u (torusGraph_adj_right v.1 v.2) =
      regularDirectedTransport u (torusGraph_adj_right v.1 (v.2 + 1)) *
        regularDirectedTransport u (torusGraph_adj_up v.1 v.2) := by
  let A := regularDirectedTransport u (torusGraph_adj_right v.1 v.2)
  let B := regularDirectedTransport u (torusGraph_adj_up v.1 v.2)
  let C := regularDirectedTransport u (torusGraph_adj_up (v.1 + 1) v.2)
  let D := regularDirectedTransport u (torusGraph_adj_right v.1 (v.2 + 1))
  change regularWalkHolonomy u (torusPlaquetteWalk v) = 1 ↔ C * A = D * B
  simp only [torusPlaquetteWalk, regularWalkHolonomy_cons, regularWalkHolonomy_nil,
    one_mul]
  rw [regularDirectedTransport_symm u (torusGraph_adj_up v.1 v.2),
    regularDirectedTransport_symm u (torusGraph_adj_right v.1 (v.2 + 1))]
  change ((B⁻¹ * D⁻¹) * C) * A = 1 ↔ C * A = D * B
  rw [show ((B⁻¹ * D⁻¹) * C) * A = (D * B)⁻¹ * (C * A) by group,
    inv_mul_eq_one, eq_comm]

/-- The native directed transports of every nonzero inserted state satisfying
all original plaquette parent conditions are flat in the torus transport
sense. Source: SCP10, necessary local closure constraint in Theorem 5.5,
lines 1440–1514, and string deformation, lines 1622–1647. -/
theorem IsGInjective.isTorusFlat_of_parentHamiltonian_annihilates_twistedState
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (u : Edge Γₜ → G)
    (Q : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hQ : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (Q v))
    (hne : stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) ≠ 0)
    (hground : regionParentHamiltonian torusPlaquetteRegion Q *ᵥ
      stateCoeff (groupBondTensor (regularTwistedSite (torusIncidentSite a) u)) = 0) :
    IsTorusFlat (fun v => regularDirectedTransport u (torusGraph_adj_right v.1 v.2))
      (fun v => regularDirectedTransport u (torusGraph_adj_up v.1 v.2)) := by
  intro v
  exact (torusPlaquetteHolonomy_eq_one_iff_squareTransport u v).mp
    (ha.torusPlaquetteHolonomy_eq_one_of_parentHamiltonian_annihilates u Q hQ hne hground v)

end TNLean.PEPS
