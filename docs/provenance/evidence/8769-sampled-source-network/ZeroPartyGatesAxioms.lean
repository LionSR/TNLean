import TNLeanReduction.ZeroPartyGates

/-! Kernel dependencies of gates on no participating parties. -/

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
set_option linter.hashCommand false in
#check
  @TNLean.PEPS.PairEffect.SourceCircuit.eval_gate_heq_coeffSum_smul_id_of_participants_eq_empty
