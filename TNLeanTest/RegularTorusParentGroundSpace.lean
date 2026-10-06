/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.TorusRegularParentGroundSpace

/-!
# Regular torus parent-kernel signatures and axioms

The full-kernel conclusions require neither isometry nor a supplied closure
expansion. The dimension counts simultaneous conjugacy classes of commuting
pairs, for the complete native plaquette family and both periods at least three.
-/

open TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

example {a : G → G → G → G → Fin d → ℂ}
    (ha : IsGInjective (torusLegRep (leftRegularMatrix G)) (siteMap a))
    (P : (v : TorusVertex width height) →
      Matrix (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v))
        (RegionPhysicalConfig (d := d) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (groupBondTensor (torusIncidentSite a))
      (torusPlaquetteRegion v) (P v)) :
    Module.finrank ℂ (Matrix.mulVecLin
      (regionParentHamiltonian torusPlaquetteRegion P)).ker =
        Nat.card (CommutingPairConjugacyClass G) :=
  ha.finrank_torusParentKernel P hP

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.eq_sum_supported_regularProjectorClosedState_of_invariant'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.eq_sum_supported_regularProjectorClosedState_of_invariant

/--
info: 'TNLean.PEPS.exists_regularVertexGauge_eq_torusClosure'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_regularVertexGauge_eq_torusClosure

/--
info: 'TNLean.PEPS.IsGInjective.exists_torusParentCoordinates'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGInjective.exists_torusParentCoordinates

/--
info: 'TNLean.PEPS.IsGInjective.torusParentKernel_le_commutingClosureSpan'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGInjective.torusParentKernel_le_commutingClosureSpan

/--
info: 'TNLean.PEPS.isSimplyConnected_torusRegionRealization_plaquette'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.isSimplyConnected_torusRegionRealization_plaquette

/--
info: 'TNLean.PEPS.IsGInjective.torusParentKernel_eq_commutingClosureSpan'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGInjective.torusParentKernel_eq_commutingClosureSpan

/--
info: 'TNLean.PEPS.IsGInjective.finrank_torusParentKernel'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.IsGInjective.finrank_torusParentKernel
