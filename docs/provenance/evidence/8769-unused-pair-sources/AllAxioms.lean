/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CompletePartyMaps

/-!
# Imported axiom audit for completion of unused pair sources

This audit checks every explicit public declaration in the three new modules.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.PairSource.unit
#print axioms TNLean.PEPS.PairEffect.PairSource.partyPair_unit
#print axioms TNLean.PEPS.PairEffect.PairSource.norm_unit_vector
#print axioms TNLean.PEPS.PairEffect.PairSource.finrank_unit_spaces
#print axioms TNLean.PEPS.PairEffect.Word.eraseUnitPair
#print axioms TNLean.PEPS.PairEffect.Word.eraseUnitPair_spec
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands.unit_cons
#print axioms TNLean.PEPS.PairEffect.SourceInventory.exists_complete_extension
#print axioms TNLean.PEPS.PairEffect.SourceInventory.exists_complete
#print axioms TNLean.PEPS.PairEffect.Word.exists_complete_source_preparation
#print axioms TNLean.PEPS.PairEffect.Word.exists_complete_prepared_tensorPartyMaps

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-unused-pair"
  IO.FS.writeFile (directory / "final-verification-20261007" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
