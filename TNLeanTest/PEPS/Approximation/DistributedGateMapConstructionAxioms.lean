/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedGateMapConstruction

/-!
# Axiom checks for the compression of distributed constructions

These checks cover the public declarations of the reading of a distributed construction
with the operators of its own expansions, Theorem 5.2 for such families, and Remark 5.3.
-/

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.PairEffect.EffectCircuit.expansionGateMaps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.EffectCircuit.expansionGateMaps

/--
info: 'TNLean.PEPS.PairEffect.EffectCircuit.expansionGateLists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.EffectCircuit.expansionGateLists

/--
info: 'TNLean.PEPS.PairEffect.EffectCircuit.evalWithGateMaps_expansionGateMaps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.EffectCircuit.evalWithGateMaps_expansionGateMaps

/--
info: 'TNLean.PEPS.PairEffect.OriginalCircuit.IsTermwiseBounded.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.OriginalCircuit.IsTermwiseBounded.mono

/--
info: 'TNLean.PEPS.PairEffect.OriginalCircuit.isGateApproximation_reexpand_expansionGateLists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.OriginalCircuit.isGateApproximation_reexpand_expansionGateLists

/--
info: 'TNLean.PEPS.PairEffect.OriginalCircuit.isTermwiseBounded_reexpand_expansionGateLists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.OriginalCircuit.isTermwiseBounded_reexpand_expansionGateLists

/--
info: 'TNLean.PEPS.PairEffect.OriginalCircuit.monomialCount_reexpand_expansionGateLists_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.OriginalCircuit.monomialCount_reexpand_expansionGateLists_le

/--
info: 'TNLean.PEPS.PairEffect.OriginalCircuit.natCard_participation_produce' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.OriginalCircuit.natCard_participation_produce

/--
info: 'TNLean.PEPS.PairEffect.DistributedConstruction.toGateMapConstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.toGateMapConstruction

/--
info: 'TNLean.PEPS.PairEffect.DistributedConstruction.physicalDensity_toGateMapConstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.physicalDensity_toGateMapConstruction

/--
info: 'TNLean.PEPS.PairEffect.DistributedConstruction.uniform_sampled_network_of_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.uniform_sampled_network_of_sum_le

/--
info: 'TNLean.PEPS.PairEffect.DistributedConstruction.uniform_sampled_network_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.uniform_sampled_network_of_le

/--
info: 'TNLean.PEPS.PairEffect.DistributedConstruction.exists_uniform_sampled_network' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.exists_uniform_sampled_network

open TNLean.PEPS.PairEffect.DistributedConstruction in
/--
info: 'TNLean.PEPS.PairEffect.DistributedConstruction.exists_uniform_sampled_network_sub_pure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_uniform_sampled_network_sub_pure_le
