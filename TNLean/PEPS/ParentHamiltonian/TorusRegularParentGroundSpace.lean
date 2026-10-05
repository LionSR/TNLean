/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusPlaquetteParentSupport
import TNLean.PEPS.ParentHamiltonian.TorusRegularParentSpanning

/-!
# Full native plaquette parent ground space

For a regular G-injective tensor, the kernel of the complete native positive
plaquette parent Hamiltonian equals the span of its commuting torus closures.
Its dimension is the number of simultaneous conjugacy classes of commuting
pairs. Both torus periods are at least three; no isometry or prior expansion
of a ground state is assumed.

Source: SCP10, arXiv:1001.3807, Theorems 5.7 and 5.9, specialized to the regular
representation and native tori of periods at least three.

**Scope restriction (regular native torus):** The virtual representation is regular
and both periods are at least three. The semi-regular parent-kernel and
smaller-period statements remain separate; see
`docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- The full positive native plaquette parent kernel is exactly the commuting
closure span. Source: SCP10, Theorem 5.7, regular native-torus specialization. -/
theorem IsGInjective.torusParentKernel_eq_commutingClosureSpan
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker =
      Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
        torusGClosure (width := width) (height := height)
          (leftRegularMatrix G) a p.1.1 p.1.2)) :=
  le_antisymm (ha.torusParentKernel_le_commutingClosureSpan P hP)
    (ha.commutingClosureSpan_le_torusParentKernel P hP)

/-- The full native plaquette parent ground-space dimension is the number of
simultaneous conjugacy classes of commuting pairs. Source: SCP10, Theorem 5.9,
regular native-torus specialization. -/
theorem IsGInjective.finrank_torusParentKernel
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    Module.finrank ℂ (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker =
      Nat.card (CommutingPairConjugacyClass G) := by
  rw [ha.torusParentKernel_eq_commutingClosureSpan P hP,
    range_torusGClosure_commuting_eq_range_torusGClosureClass _ _ ha.invariant]
  exact ha.finrank_span_torusGClosureClass_commuting_of_isSemiRegular
    (isSemiRegular_leftRegularMatrix (G := G))

end TNLean.PEPS
