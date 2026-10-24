/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.DistributedGateMapConstruction

/-!
# Axiom checks for the compression of distributed constructions

These checks cover the public declarations of the reading of a distributed construction
with the operators of its own expansions, Theorem 5.2 for such families, and Remark 5.3.
-/

set_option linter.hashCommand false

/--
info: 'TNLean.Lattice.PartyCircuit.EffectCircuit.expansionGateMaps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.EffectCircuit.expansionGateMaps

/--
info: 'TNLean.Lattice.PartyCircuit.EffectCircuit.expansionGateLists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.EffectCircuit.expansionGateLists

/--
info: 'TNLean.Lattice.PartyCircuit.EffectCircuit.evalWithGateMaps_expansionGateMaps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.EffectCircuit.evalWithGateMaps_expansionGateMaps

/--
info: 'TNLean.Lattice.PartyCircuit.OriginalCircuit.IsTermwiseBounded.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.OriginalCircuit.IsTermwiseBounded.mono

/--
info: 'TNLean.Lattice.PartyCircuit.OriginalCircuit.isGateApproximation_reexpand_expansionGateLists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open TNLean.Lattice.PartyCircuit in
#print axioms OriginalCircuit.isGateApproximation_reexpand_expansionGateLists

/--
info: 'TNLean.Lattice.PartyCircuit.OriginalCircuit.isTermwiseBounded_reexpand_expansionGateLists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open TNLean.Lattice.PartyCircuit in
#print axioms OriginalCircuit.isTermwiseBounded_reexpand_expansionGateLists

/--
info: 'TNLean.Lattice.PartyCircuit.OriginalCircuit.monomialCount_reexpand_expansionGateLists_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open TNLean.Lattice.PartyCircuit in
#print axioms OriginalCircuit.monomialCount_reexpand_expansionGateLists_le

/--
info: 'TNLean.Lattice.PartyCircuit.OriginalCircuit.natCard_participation_produce' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.OriginalCircuit.natCard_participation_produce

/--
info: 'TNLean.Lattice.PartyCircuit.DistributedConstruction.toGateMapConstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.DistributedConstruction.toGateMapConstruction

/--
info: 'TNLean.Lattice.PartyCircuit.DistributedConstruction.physicalDensity_toGateMapConstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
open TNLean.Lattice.PartyCircuit in
#print axioms DistributedConstruction.physicalDensity_toGateMapConstruction

/--
info: 'TNLean.Lattice.PartyCircuit.DistributedConstruction.uniform_sampled_network_of_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.DistributedConstruction.uniform_sampled_network_of_sum_le

/--
info: 'TNLean.Lattice.PartyCircuit.DistributedConstruction.uniform_sampled_network_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.DistributedConstruction.uniform_sampled_network_of_le

/--
info: 'TNLean.Lattice.PartyCircuit.DistributedConstruction.exists_uniform_sampled_network' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.Lattice.PartyCircuit.DistributedConstruction.exists_uniform_sampled_network

open TNLean.Lattice.PartyCircuit.DistributedConstruction in
/--
info: 'TNLean.Lattice.PartyCircuit.DistributedConstruction.exists_uniform_sampled_network_sub_pure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_uniform_sampled_network_sub_pure_le
