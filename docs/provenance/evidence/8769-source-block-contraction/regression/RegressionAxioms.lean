import SourceBlockRegression

/-! # Imported audit of the free-source block regressions. -/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.SourceBlockRegression.rectangular_imaginary_input
#print axioms TNLean.PEPS.PairEffect.SourceBlockRegression.empty_sources_identity

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "/private/tmp/tnlean-source-block-regression-evidence/imported-modules.json"
    (Lean.Json.compress (Lean.Json.arr names))
