import FixedSourceRegression

/-! Imported audit of the genuine-source chronological regression. -/
set_option linter.hashCommand false

namespace TNLean.PEPS.PairEffect.FixedSourceRegression
#print axioms repeated_local_labels
#print axioms repeated_fixed_source_vectors
#print axioms actual_source_inventory_nonempty
end TNLean.PEPS.PairEffect.FixedSourceRegression

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath :=
    "/private/tmp/tnlean-fixed-chronological-sources-regression-evidence"
  IO.FS.writeFile (directory / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
