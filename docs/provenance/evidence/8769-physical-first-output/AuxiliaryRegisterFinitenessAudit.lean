import TNLeanRelayOutput.AuxiliaryRegisterFiniteness

/-! # Stock axiom audit of all public declarations -/

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.Layout.finiteDimensional_registers_append

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.Layout.finiteDimensional_registers_mapOwner

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.finiteDimensional_registers_sources_comp

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.finiteDimensional_registers_sources_prepWord

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.PartyChain.finiteDimensional_registers_sources_prepStack

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.finiteDimensional_registers_sources_prepGate

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.EffectCircuit.finiteDimensional_auxiliary_registers

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.EffectCircuit.finiteDimensional_auxiliary_private_registers

set_option linter.hashCommand false in
#print axioms TNLean.PEPS.PairEffect.EffectCircuit.finiteDimensional_auxiliary_private_mem
