import TNLeanRelayOutput.SampledOriginalCircuit

/-! # Stock axiom audit of all public sampling declarations -/

namespace TNLean.PEPS.PairEffect.OriginalCircuit

set_option linter.hashCommand false in
#print axioms isMonomialBounded_mono

set_option linter.hashCommand false in
#print axioms exists_isMonomialBounded

set_option linter.hashCommand false in
#print axioms sum_norm_branchCoefficient_physicalFirstReplacement_le

set_option linter.hashCommand false in
#print axioms exists_physicalFirst_sourceSample_original_error_le

end TNLean.PEPS.PairEffect.OriginalCircuit
