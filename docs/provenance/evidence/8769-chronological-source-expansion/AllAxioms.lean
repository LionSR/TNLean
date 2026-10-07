/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedSourceComposition
import TNLean.PEPS.Approximation.PartialSourceEvaluation
import TNLean.PEPS.Approximation.PartialSourceInventory
import TNLean.PEPS.Approximation.SourceChoiceCost
import TNLean.PEPS.Approximation.SourceCircuitLocations
import TNLean.PEPS.Approximation.PartialSourceDensity
import TNLean.PEPS.Approximation.SourceCircuitChoiceProduct
import TNLean.PEPS.Approximation.SourceCircuitSourceOrder

/-!
# Imported axiom audit for chronological partial source expansions

This audit checks every explicit public declaration in the eight new modules.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.SourceCircuit
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.eval
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.IsAllowed
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.norm_eval_le_one
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.Choices
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.choicesFintype
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.partialWord
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.coefficient
#print axioms TNLean.PEPS.PairEffect.Word.eval_sum_appendTail
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.eval_partial_gate
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.expandedEval
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.expandedEval_comp
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.expandedEval_frame
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.expandedEval_mapOwner
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.isAllowed_partialWord
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.expandedSources
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sources_partialWord
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.mem_sources_partialWord
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_gate_of_touches
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_gate_of_exterior
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_comp
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_frame
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_id
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_localMap
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_swap
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.gateLocations
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.gateLocationsFintype
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.slotCount
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sourceLocations
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sourceLocationsFintype
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.participants
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.endpoints
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.endpoints_mem_participants
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.endpoints_ne
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.branchLabels
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.branchLabelsFintype
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.branchCoefficient
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.IsTouched
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.isTouched_gate_iff
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_eq_prod
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_le_pow_card
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_mul_conj_eq_prod_sq
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sum_norm_coefficient_mul_conj_le_pow_card
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.expandedEval_eq_mapOwner
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.toMatrix_eval_eq_sum_partialWord
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.density_eval_eq_sum_partialWord
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sourceOrder
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.mem_sourceOrder
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.nodup_sourceOrder
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sourceDims
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sourceAt
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sourceAt_isSome_iff
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sourceAt_eq_some_spec
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.sources_partialWord_eq_filterMap
#print axioms TNLean.PEPS.PairEffect.SourceCircuit.layout_sources_partialWord

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-chronological-source"
  IO.FS.writeFile (directory / "final-verification-20261007" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
