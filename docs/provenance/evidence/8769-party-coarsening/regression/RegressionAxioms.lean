import PartyCoarseningRegression

/-! # Imported audit of the grouping-of-parties regressions. -/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.PartyCoarseningRegression.two_occurrences_one_pair
#print axioms TNLean.PEPS.PairEffect.PartyCoarseningRegression.internal_phase_source

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "/private/tmp/tnlean-party-coarsening-regression-evidence/imported-modules.json"
    (Lean.Json.compress (Lean.Json.arr names))
