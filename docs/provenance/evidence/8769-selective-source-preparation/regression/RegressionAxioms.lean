import SelectiveSourceRegressions

/-! # Imported audit of selective preparation and factorization regressions. -/

set_option linter.hashCommand false

#print axioms SelectiveSourceRegressions.fixed_normalized
#print axioms SelectiveSourceRegressions.mixed_free_layout
#print axioms SelectiveSourceRegressions.mixed_fixed_order
#print axioms SelectiveSourceRegressions.all_free_sources
#print axioms SelectiveSourceRegressions.all_fixed_sources
#print axioms SelectiveSourceRegressions.all_fixed_input
#print axioms SelectiveSourceRegressions.mixed_recovery
#print axioms SelectiveSourceRegressions.mixed_allowed
#print axioms SelectiveSourceRegressions.mixed_internal
#print axioms SelectiveSourceRegressions.mixed_partition

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile
    ("/private/tmp/tnlean-selective-source-preparation-regression-evidence/" ++
      "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
