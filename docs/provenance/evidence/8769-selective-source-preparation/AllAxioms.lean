/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AffectedOwners
import TNLean.PEPS.Approximation.GroupedBlockMap
import TNLean.PEPS.Approximation.SelectiveSourcePreparation
import TNLean.PEPS.Approximation.WordAppendTail
import TNLean.PEPS.Approximation.PreparedSourceGate
import TNLean.PEPS.Approximation.SelectiveSourceFactorization

/-!
# Imported axiom audit for selective source preparations and operations beside spectators

This audit checks every explicit public declaration in the six new modules.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.affectedOwner
#print axioms TNLean.PEPS.PairEffect.affectedOwner_eq_none
#print axioms TNLean.PEPS.PairEffect.affectedOwner_eq_iff
#print axioms TNLean.PEPS.PairEffect.PairSource.affectedOwner_ne_iff
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mem_mapOwner_affectedOwner
#print axioms TNLean.PEPS.PairEffect.SourceInventory.map_partyPair_affectedOwner
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mapOwner_affectedOwner_eq_nil_iff
#print axioms TNLean.PEPS.PairEffect.Word.groupedBlockMap
#print axioms TNLean.PEPS.PairEffect.Word.groupedBlockMap_spec
#print axioms TNLean.PEPS.PairEffect.Word.eval_groupedBlockMap
#print axioms TNLean.PEPS.PairEffect.Word.eval_sum_mapOwner_comp
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate.branchWord
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate.eval
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate.branchWord_isAllowed
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate.sources_branchWord
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate.norm_eval_le_one
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate.evalAtOwners
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate.evalAtOwners_eq_sum
#print axioms TNLean.PEPS.PairEffect.PreparedSourceGate.norm_evalAtOwners_le_one
#print axioms TNLean.PEPS.PairEffect.Word.exists_preparedSourceGate
#print axioms TNLean.PEPS.PairEffect.SourceInventory.selectedSources
#print axioms TNLean.PEPS.PairEffect.SourceInventory.layout_selectedSources_eq
#print axioms TNLean.PEPS.PairEffect.SourceInventory.freeSlotLayout
#print axioms TNLean.PEPS.PairEffect.SourceInventory.prepareSelected
#print axioms TNLean.PEPS.PairEffect.SourceInventory.prepareFreeSlots
#print axioms TNLean.PEPS.PairEffect.SourceInventory.fillSourceVectors
#print axioms TNLean.PEPS.PairEffect.SourceInventory.isAllowed_prepareSelected
#print axioms TNLean.PEPS.PairEffect.SourceInventory.sources_prepareSelected
#print axioms TNLean.PEPS.PairEffect.SourceInventory.eval_prepareSelected_prepareFreeSlots
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mem_selectedSources
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mem_sources_prepareSelected
#print axioms TNLean.PEPS.PairEffect.Word.exists_selective_partition
#print axioms TNLean.PEPS.PairEffect.Word.appendTail
#print axioms TNLean.PEPS.PairEffect.Word.isAllowed_appendTail
#print axioms TNLean.PEPS.PairEffect.Word.sources_appendTail
#print axioms TNLean.PEPS.PairEffect.Word.eval_appendTail

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-selective-source-preparation"
  IO.FS.writeFile (directory / "final-verification-20261007" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
