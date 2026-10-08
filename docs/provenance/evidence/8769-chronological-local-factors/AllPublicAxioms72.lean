import TNLeanRelayNetwork.ChronologicalLocality
import TNLeanRelayNetwork.UntouchedResidual
import TNLeanRelayNetwork.InvisibleRestriction
import TNLeanRelayNetwork.FullResidualLocality
import TNLeanRelayNetwork.FullBranchPreparation
import TNLeanRelayNetwork.FullChronologicalPreparation
import TNLeanRelayNetwork.AbsorbedRestriction
import TNLeanRelayNetwork.CanonicalPartyFactorization
import TNLeanRelayNetwork.ChronologicalPartyFactorization
import TNLeanRelayNetwork.SourcefulInvisibleRestriction
import TNLeanRelayNetwork.ResidualRestrictionCongruence
import TNLeanRelayNetwork.AllChoicesProjection
import TNLeanRelayNetwork.AllPartialGate
import TNLeanRelayNetwork.PartialResidualLocality
import TNLeanRelayNetwork.TouchedLabels
import TNLeanRelayNetwork.NonemptyGateLabels
import TNLeanRelayNetwork.PointwiseChoiceCoefficient
import TNLeanRelayNetwork.ActualPartialLocalMaps
import TNLeanRelayNetwork.ActualPartialPartyFactorization
import TNLeanRelayNetwork.ActualSourceLocalMaps

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms FullLabels

set_option linter.hashCommand false in
#print axioms choicesOfFullLabels

set_option linter.hashCommand false in
#print axioms choicesOfFullLabels_eq_of_agree

set_option linter.hashCommand false in
#print axioms choiceAt_choicesOfFullLabels

set_option linter.hashCommand false in
#print axioms partySelector

set_option linter.hashCommand false in
#print axioms choicesOfFullLabels_party_eq_of_agree

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.Word
set_option linter.hashCommand false in
#print axioms parties_mapOwner_of_sources_nil

set_option linter.hashCommand false in
#print axioms restrict_mapOwner_eval_eq_id_of_disjoint

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.PreparedSourceGate
set_option linter.hashCommand false in
#print axioms restrict_remaining_appendTail_eval_eq_id_of_not_participating

set_option linter.hashCommand false in
#print axioms restrict_remaining_appendTail_eq_of_not_participating

end TNLean.PEPS.PairEffect.PreparedSourceGate

namespace TNLean.PEPS.PairEffect.Word
set_option linter.hashCommand false in
#print axioms restrict_mapOwner_appendTail_eval_eq_id_of_disjoint

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms fixedSourceLayout

set_option linter.hashCommand false in
#print axioms fullRemainingWord

set_option linter.hashCommand false in
#print axioms sources_fullRemainingWord

set_option linter.hashCommand false in
#print axioms isAllowed_fullRemainingWord

set_option linter.hashCommand false in
#print axioms restrict_fullRemainingWord_eq_of_agree

set_option linter.hashCommand false in
#print axioms restrict_fullRemainingWord_eq_of_choices_eq

set_option linter.hashCommand false in
#print axioms localRemainingMap

set_option linter.hashCommand false in
#print axioms restrict_fullRemainingWord_eq_localRemainingMap

set_option linter.hashCommand false in
#print axioms norm_localRemainingMap_le_one

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms fullBranchWord

set_option linter.hashCommand false in
#print axioms fullSourceVector

set_option linter.hashCommand false in
#print axioms fullRemainingWord_gate_prepare_tmul

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms fullRemainingWord_gate_prepare

set_option linter.hashCommand false in
#print axioms fullRemainingWord_prepare

set_option linter.hashCommand false in
#print axioms eval_fullBranchWord_eq_fullRemainingWord

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.Word
set_option linter.hashCommand false in
#print axioms restrict_restrict_heq_of_implies

set_option linter.hashCommand false in
#print axioms restrict_restrict_eval_heq_of_implies

set_option linter.hashCommand false in
#print axioms restrict_withoutParty_atParty_eval_heq

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.Word
set_option linter.hashCommand false in
#print axioms groupByPartyIso_eval_eq_tensorRestrictions

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms groupByPartyIso_fullRemainingWord_eq_tensorLocalRemainingMaps

set_option linter.hashCommand false in
#print axioms groupByPartyIso_fullBranchWord_eq_tensorLocalRemainingMaps

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.Word
set_option linter.hashCommand false in
#print axioms restrict_localPart_mapOwner_appendTail_mapOwner_eval_eq_id_of_disjoint

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.Word
set_option linter.hashCommand false in
#print axioms restrict_castInput_eval_heq

set_option linter.hashCommand false in
#print axioms restrict_comp_eval_heq

set_option linter.hashCommand false in
#print axioms restrict_frame_eval_heq

set_option linter.hashCommand false in
#print axioms restrict_frameList_eval_heq

set_option linter.hashCommand false in
#print axioms restrict_localPart_comp_eval_heq

set_option linter.hashCommand false in
#print axioms restrict_moveHead_eval_heq

set_option linter.hashCommand false in
#print axioms restrict_localPart_frame_eval_heq

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms projectAllChoices

set_option linter.hashCommand false in
#print axioms choiceAt_projectAllChoices

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms partialWord_all_gate_eq_of_touched

set_option linter.hashCommand false in
#print axioms partialWord_all_gate_eq_of_untouched

set_option linter.hashCommand false in
#print axioms restrict_partialWord_all_gate_localPart_eval_heq_id_of_disjoint

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms restrict_partialWord_localPart_eval_heq_of_projectAllChoices_eq

set_option linter.hashCommand false in
#print axioms restrict_partialResidual_eval_eq_of_projectAllChoices_eq

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms TouchedLabels

set_option linter.hashCommand false in
#print axioms choicesOfTouchedLabels

set_option linter.hashCommand false in
#print axioms choiceAt_choicesOfTouchedLabels

set_option linter.hashCommand false in
#print axioms choicesOfTouchedLabels_choiceAt

set_option linter.hashCommand false in
#print axioms choicesTouchedLabelsEquiv

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms isTouched_all_iff

set_option linter.hashCommand false in
#print axioms nonemptyGateLocations

set_option linter.hashCommand false in
#print axioms nonemptyGateLocationsFintype

set_option linter.hashCommand false in
#print axioms allChoicesNonemptyLabelsEquiv

set_option linter.hashCommand false in
#print axioms allChoicesNonemptyLabelsEquiv_apply

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms coefficient_eq_prod_dite

set_option linter.hashCommand false in
#print axioms coefficient_all_eq_prod_nonemptyGateLocations

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms allResidualInput

set_option linter.hashCommand false in
#print axioms partialLocalRemainingMap

set_option linter.hashCommand false in
#print axioms restrict_partialResidual_eq_partialLocalRemainingMap

set_option linter.hashCommand false in
#print axioms norm_partialLocalRemainingMap_le_one

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms groupByPartyIso_partialResidual_eq_tensorPartialLocalRemainingMaps

end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
set_option linter.hashCommand false in
#print axioms allResidualSourceLayout

set_option linter.hashCommand false in
#print axioms sourcePrivatePreparation

set_option linter.hashCommand false in
#print axioms sources_sourcePrivatePreparation

set_option linter.hashCommand false in
#print axioms partialSourceWord

set_option linter.hashCommand false in
#print axioms sources_partialSourceWord

set_option linter.hashCommand false in
#print axioms partialSourceLocalMap

set_option linter.hashCommand false in
#print axioms restrict_partialSourceWord_eq_partialSourceLocalMap

set_option linter.hashCommand false in
#print axioms groupByPartyIso_partialSourceWord_eq_tensorPartialSourceLocalMaps

end TNLean.PEPS.PairEffect.SourceCircuit

