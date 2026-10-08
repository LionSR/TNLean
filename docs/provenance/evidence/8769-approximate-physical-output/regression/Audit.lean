import ApproximateGateRegression
set_option linter.hashCommand false

namespace TNLean.PEPS.PairEffect.ApproximateGateRegression
#print axioms raw_scalar_norm_two
end TNLean.PEPS.PairEffect.ApproximateGateRegression

namespace TNLean.PEPS.PairEffect.ApproximateGateRegression
#print axioms scalar_isGateApproximation
end TNLean.PEPS.PairEffect.ApproximateGateRegression

namespace TNLean.PEPS.PairEffect.ApproximateGateRegression
#print axioms repeated_scalar_count
end TNLean.PEPS.PairEffect.ApproximateGateRegression

namespace TNLean.PEPS.PairEffect.ApproximateGateRegression
#print axioms rescaled_scalar_operator
end TNLean.PEPS.PairEffect.ApproximateGateRegression

run_cmd do
  let e ← Lean.getEnv
  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))
