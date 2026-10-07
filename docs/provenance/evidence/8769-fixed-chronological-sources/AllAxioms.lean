/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartialSourcePreparation
import TNLean.PEPS.Approximation.WordSelectivePartition
import TNLean.PEPS.Approximation.SourceCircuitChoiceAt

/-!
# Imported axiom audit for fixed chronological source preparation

This audit checks every explicit public declaration in the three new modules.
-/

set_option linter.hashCommand false

namespace TNLean.PEPS.PairEffect

#print axioms SourceCircuit.partialPositions
#print axioms SourceCircuit.mem_partialPositions_iff
#print axioms SourceCircuit.partialSlots
#print axioms SourceCircuit.partialSlotEquiv
#print axioms SourceCircuit.partialSlotEquiv_apply
#print axioms SourceCircuit.layout_partialSlots
#print axioms SourceCircuit.partialSlot_spec
#print axioms SourceCircuit.layout_partialSlots_eq
#print axioms SourceCircuit.exists_partial_source_preparation
#print axioms SourceCircuit.choiceAt
#print axioms SourceCircuit.sourceVectorAt
#print axioms SourceCircuit.sourceVectorAt_norm
#print axioms SourceCircuit.isTouched_of_source_endpoint
#print axioms SourceCircuit.sourceAt_eq_mapOwner_sourceVectorAt
#print axioms SourceCircuit.partialSlotChoice
#print axioms SourceCircuit.partialSlotVector
#print axioms SourceCircuit.eq_partialSlotVector_of_inventory_eq
#print axioms SourceCircuit.exists_partial_source_preparation_with_original_vectors
#print axioms Word.exists_selective_partition_of_word

end TNLean.PEPS.PairEffect

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-fixed-chronological-sources"
  IO.FS.writeFile (directory / "final-verification-20261008" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
