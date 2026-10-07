/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation

/-!
# Complete axiom audit of the finite distributed-compression results

This audits all 47 named public definitions and theorems in DistributedLifetime,
DistributedLinks and CorrectedPositionCost through their generated public import.
It makes no assertion about the complete distributed density-compression theorem.
-/

#print axioms TNLean.PEPS.Approximation.ketBraCoefficientCost
#print axioms TNLean.PEPS.Approximation.ketBraCoefficientCost_eq_sum
#print axioms TNLean.PEPS.Approximation.correctedPositionChoiceCost
#print axioms TNLean.PEPS.Approximation.correctedPositionChoiceCost_le
#print axioms TNLean.PEPS.Approximation.compressionChoiceBase_le_of_monomial_bounds
#print axioms TNLean.PEPS.Approximation.sourceEndpoints
#print axioms TNLean.PEPS.Approximation.correctedParties
#print axioms TNLean.PEPS.Approximation.incidentGates
#print axioms TNLean.PEPS.Approximation.gatesTouching
#print axioms TNLean.PEPS.Approximation.mem_sourceEndpoints
#print axioms TNLean.PEPS.Approximation.mem_correctedParties
#print axioms TNLean.PEPS.Approximation.mem_incidentGates
#print axioms TNLean.PEPS.Approximation.mem_gatesTouching
#print axioms TNLean.PEPS.Approximation.card_sourceEndpoints_le
#print axioms TNLean.PEPS.Approximation.card_correctedParties_le
#print axioms TNLean.PEPS.Approximation.card_gatesTouching_le
#print axioms TNLean.PEPS.Approximation.card_gatesTouching_correctedParties_le
#print axioms TNLean.PEPS.Approximation.owner_mem_gatesTouching_correctedParties
#print axioms TNLean.PEPS.Approximation.disjoint_participants_of_not_mem_gatesTouching
#print axioms TNLean.PEPS.Approximation.pairSampleLabels
#print axioms TNLean.PEPS.Approximation.gateLinkLabels
#print axioms TNLean.PEPS.Approximation.gateLinkParties
#print axioms TNLean.PEPS.Approximation.linksAtGate
#print axioms TNLean.PEPS.Approximation.distributedLinks
#print axioms TNLean.PEPS.Approximation.distributedLinkParties
#print axioms TNLean.PEPS.Approximation.incidentDistributedLinks
#print axioms TNLean.PEPS.Approximation.incidentGateLinkLabels
#print axioms TNLean.PEPS.Approximation.incidentLinksAtGate
#print axioms TNLean.PEPS.Approximation.mem_pairSampleLabels
#print axioms TNLean.PEPS.Approximation.mk_mem_pairSampleLabels
#print axioms TNLean.PEPS.Approximation.card_pairSampleLabels
#print axioms TNLean.PEPS.Approximation.filter_pairSampleLabels_eq_map
#print axioms TNLean.PEPS.Approximation.card_filter_pairSampleLabels
#print axioms TNLean.PEPS.Approximation.card_gateLinkLabels
#print axioms TNLean.PEPS.Approximation.card_gateLinkLabels_le
#print axioms TNLean.PEPS.Approximation.card_incidentGateLinkLabels_le
#print axioms TNLean.PEPS.Approximation.gateLinkParties_subset
#print axioms TNLean.PEPS.Approximation.card_gateLinkParties
#print axioms TNLean.PEPS.Approximation.card_linksAtGate
#print axioms TNLean.PEPS.Approximation.mem_linksAtGate
#print axioms TNLean.PEPS.Approximation.card_incidentLinksAtGate
#print axioms TNLean.PEPS.Approximation.mem_distributedLinks
#print axioms TNLean.PEPS.Approximation.distributedLinkParties_subset
#print axioms TNLean.PEPS.Approximation.card_distributedLinkParties
#print axioms TNLean.PEPS.Approximation.exists_common_gate_of_mem_distributedLinkParties
#print axioms TNLean.PEPS.Approximation.incidentDistributedLinks_subset
#print axioms TNLean.PEPS.Approximation.card_incidentDistributedLinks_le
