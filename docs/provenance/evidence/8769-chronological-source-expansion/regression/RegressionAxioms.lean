import SourceCircuitRegression

/-! # Imported audit of the chronological gate regressions. -/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.SourceCircuitRegression.exterior_empty_branch
#print axioms TNLean.PEPS.PairEffect.SourceCircuitRegression.repeated_touching_choices
#print axioms TNLean.PEPS.PairEffect.SourceCircuitRegression.phase_partial_expansion

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/private/tmp"
  IO.FS.writeFile (directory / "tnlean-chronological-source-expansion-regression-evidence" /
    "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
