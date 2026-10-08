import TNLean.PEPS.Approximation.DistributedConstruction
set_option linter.hashCommand false
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.input
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.physicalDensity
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.physicalDensity_posSemidef
#print axioms TNLean.PEPS.PairEffect.DistributedConstruction.trace_physicalDensity_le_one

run_cmd do
  let e ← Lean.getEnv
  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))
