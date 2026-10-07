import TNLean.PEPS.Approximation.SourceBlockMatrix
set_option linter.hashCommand false
#print axioms TNLean.PEPS.PairEffect.Word.freeSourceMatrix
#print axioms TNLean.PEPS.PairEffect.Word.freeSourceMatrix_apply
#print axioms TNLean.PEPS.PairEffect.Word.norm_freeSourceMatrix_le_one
#print axioms TNLean.PEPS.PairEffect.Word.freeSourceMatrix_conjTranspose_mul_apply
#print axioms TNLean.PEPS.PairEffect.Word.norm_freeSourceMatrix_conjTranspose_mul_le_one
#print axioms TNLean.PEPS.PairEffect.Word.trace_preparedMatrix_mul_conjTranspose_eq
#print axioms TNLean.PEPS.PairEffect.Word.trace_preparedDensityCoefficient_eq_freeSourceMatrix
run_cmd do
  let env ← Lean.getEnv
  let names := env.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "/private/tmp/tnlean-sourceblock-style-recheck/imported-modules.json"
    (Lean.Json.compress (Lean.Json.arr names))
