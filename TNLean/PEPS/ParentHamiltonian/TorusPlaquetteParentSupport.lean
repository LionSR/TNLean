/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusPlaquetteRealization
import TNLean.PEPS.ParentHamiltonian.TorusClosureParentConstraint

/-!
# Commuting closures in the native plaquette parent kernel

Every native four-site plaquette is a topological disk, including plaquettes
crossing a seam. Consequently all commuting native closures are ground states
of the complete positive plaquette parent Hamiltonian.

Source: SCP10, arXiv:1001.3807, Theorem 5.5. The virtual representation is regular
and both native torus periods are at least three.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
local notation "X" => TorusVertex width height
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- Commuting closures belong to the full native plaquette parent kernel.
Source: SCP10, Theorem 5.5, specialized to regular native tori. -/
theorem IsGInjective.commutingClosureSpan_le_torusParentKernel
    {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : X) → Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    Submodule.span ℂ (Set.range (fun p : {p : G × G // Commute p.1 p.2} =>
      torusGClosure (width := width) (height := height)
        (leftRegularMatrix G) a p.1.1 p.1.2)) ≤
      (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker :=
  ha.span_torusGClosure_commuting_le_parentKernel torusPlaquetteRegion
    connected_torusPlaquetteRegion isSimplyConnected_torusRegionRealization_plaquette P hP

end TNLean.PEPS
