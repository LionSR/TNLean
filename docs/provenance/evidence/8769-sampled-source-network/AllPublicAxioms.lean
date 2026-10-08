import TNLeanReduction.SampledSourceNetwork
import TNLeanReduction.ZeroPartyGates

/-! Kernel dependencies of all twenty-one named public declarations. -/

set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sampledEndpointLeft
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sampledEndpointRight
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sampledSourceMatrix_eq_endpoint_average
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.card_densityBranchLabels
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourcePairAt
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourcePairAt_injective
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSlotPair
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSlotPair_bijective
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSlotPairEquiv
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSlotPairEquiv_endpoints
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSampleEquiv
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSampleEquiv_gate
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSampleEquiv_parties
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSampleIndices
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.sourceSampleIndices_apply
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.card_densityBranchLabels_le
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.card_sourceNetworkAlphabet_le
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.PreparedSourceGate.eval_heq_coeffSum_smul_id_of_isEmpty
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.PreparedSourceGate.norm_coeffSum_le_one_of_isEmpty
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.eval_gate_eq_coeffSum_smul_id_of_isEmpty
set_option linter.hashCommand false in
#print axioms
  TNLean.PEPS.PairEffect.SourceCircuit.eval_gate_heq_coeffSum_smul_id_of_participants_eq_empty
