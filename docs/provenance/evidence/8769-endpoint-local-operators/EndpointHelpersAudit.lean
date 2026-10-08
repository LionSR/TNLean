import TNLeanRelayNetwork.SourcePrivatePreparation
import TNLeanRelayNetwork.ActualSourceLocalMatrices
import TNLeanRelayNetwork.IncidentGateLabels
import TNLeanRelayNetwork.EndpointInventoryLocality
/-! # Axiom audit of actual source and endpoint operators -/
set_option linter.hashCommand false
namespace TNLean.PEPS.PairEffect.Word
#print axioms eval_frameList_tmul
#print axioms localEndpoint
#print axioms sources_localEndpoint
#print axioms eval_localEndpoint_tmul
#print axioms restrict_localEndpoint_eval_eq_of_agree
#print axioms restrict_castLayouts_eval_heq
end TNLean.PEPS.PairEffect.Word
namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms eval_sourcePrivatePreparation_tmul
#print axioms eval_partialSourceWord_tmul
#print axioms partialSourceLocalMatrix
#print axioms partialSourceLocalMatrix_eq_actual_restriction
#print axioms partialSourceLocalPhysicalMatrix
#print axioms partySelector_affectedOwner_all_apply
#print axioms isTouched_groupedParty_iff
#print axioms OriginalGateLabelsAt
#print axioms choicesOfOriginalGateLabelsAt
#print axioms originalGateLabelsAtOfAllChoices
#print axioms choicesOfOriginalGateLabelsAt_eq_projectAllChoices
end TNLean.PEPS.PairEffect.SourceCircuit
namespace TNLean.PEPS.PairEffect.SourceInventory
#print axioms endpointWord
#print axioms sources_endpointWord
#print axioms restrict_endpointWord_eval_eq_of_agree
end TNLean.PEPS.PairEffect.SourceInventory
