import TNLeanRelayNetwork.EndpointMatrixAverage
import TNLeanRelayNetwork.EndpointMatrixLocality
/-! # Axiom audit of actual endpoint coordinates and averages -/
set_option linter.hashCommand false
namespace TNLean.PEPS.PairEffect.SourceInventory
#print axioms eval_endpointWord_cons_tmul
#print axioms eval_endpointWord_slotVector_tmul
#print axioms slotVector_eq_sum_slotBasis
#print axioms slotBasis_repr_slotVector
#print axioms slotBasis_repr_endpointWord
#print axioms endpointMatrixWord
#print axioms slotBasis_repr_endpointMatrixWord
#print axioms endpointMatrixAverage_eq_product
#print axioms restrict_endpointMatrixWord_eval_eq_of_agree
end TNLean.PEPS.PairEffect.SourceInventory
namespace TNLean.PEPS.PairEffect
#print axioms basisMatrixOperator
#print axioms basisMatrixOperator_repr
end TNLean.PEPS.PairEffect
