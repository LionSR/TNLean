import TNLean

/-! Imported axiom check of the new source identities and refactored declarations. -/
set_option linter.hashCommand false

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms sourceCoordinates
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms sourceCoordinates_norm
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms exists_local_schmidt_source_frames
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms SourceGaussianSamples
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms sourceGaussianLaw
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms sourceGaussianLawIsProbabilityMeasure
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms measurePreserving_sourceGaussian_eval
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms measurePreserving_selected_sourceGaussian
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms sampledSourceMatrix
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms integrable_sampledSourceMatrix
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms integral_sampledSourceMatrix
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms exists_unbiased_sampledSourceMatrix
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms sourceGaussianCorrection
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms integral_sourceGaussianCorrection
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms sourceGaussianCorrection_eq_transport
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms physical_sampledSourceMatrix_sub_eq_sum
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms rectangularTraceNorm_physical_sampledSourceMatrix_sub_le
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms sourceCorrection_product_eq_selected
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms integrable_sourceCorrection_product_mul_conj
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms integral_sourceCorrection_product_mul_conj
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms integral_sourceCorrection_product_eq_zero
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.PairSource
#print axioms exists_probability_schmidt_isometries
end TNLean.PEPS.PairEffect.PairSource

namespace TNLean.PEPS.PairEffect.Word
#print axioms sourceContraction_preparedDensityCoefficient_selected_frames
end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms PartialSchmidtCoordinates
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms partialSchmidtCoordinateEquiv
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms partialSchmidtCoordinateEquiv_apply
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms partialSchmidtSourceVectors
end TNLean.PEPS.PairEffect.SourceCircuit

namespace TNLean.PEPS.PairEffect.SourceCircuit
#print axioms correctedSourceTerm_gaussian_eq_sum
end TNLean.PEPS.PairEffect.SourceCircuit

namespace MultilinearMap
#print axioms map_piecewise_sum_smul
end MultilinearMap

namespace TNLean.PEPS.PairEffect.Word
#print axioms sourceContraction_preparedDensityCoefficient_selected
end TNLean.PEPS.PairEffect.Word

run_cmd do
  let e ← Lean.getEnv
  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))
