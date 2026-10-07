/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CommonSourceGate
import TNLean.PEPS.Approximation.FiniteSourceGate

/-!
# Imported axiom audit for common source spaces and finite coordinates

This audit checks every explicit public declaration in the nine new modules.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.SourceInventory.ofSlots
#print axioms TNLean.PEPS.PairEffect.SourceInventory.ofSlots_nil
#print axioms TNLean.PEPS.PairEffect.SourceInventory.ofSlots_cons
#print axioms TNLean.PEPS.PairEffect.SourceInventory.isNormalized_ofSlots
#print axioms TNLean.PEPS.PairEffect.SourceInventory.layout_ofSlots_eq
#print axioms TNLean.PEPS.PairEffect.SourceInventory.partyPairs_ofSlots
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands.of_perm
#print axioms TNLean.PEPS.PairEffect.SourceInventory.exists_ofSlots_expands
#print axioms TNLean.PEPS.PairEffect.PairSource.commonSpace
#print axioms TNLean.PEPS.PairEffect.PairSource.commonInclusion
#print axioms TNLean.PEPS.PairEffect.PairSource.commonProjection
#print axioms TNLean.PEPS.PairEffect.PairSource.commonProjection_commonInclusion
#print axioms TNLean.PEPS.PairEffect.PairSource.norm_commonProjection_le
#print axioms TNLean.PEPS.PairEffect.PairSource.commonVector
#print axioms TNLean.PEPS.PairEffect.PairSource.norm_commonVector
#print axioms TNLean.PEPS.PairEffect.PairSource.mapL_commonProjection_commonVector
#print axioms TNLean.PEPS.PairEffect.Word.mapPair
#print axioms TNLean.PEPS.PairEffect.Word.mapPair_spec
#print axioms TNLean.PEPS.PairEffect.Word.eval_mapPair_tmul
#print axioms TNLean.PEPS.PairEffect.Word.eval_mapPair_source
#print axioms TNLean.PEPS.PairEffect.SourceInventory.slotLayout
#print axioms TNLean.PEPS.PairEffect.SourceInventory.prepareSlots
#print axioms TNLean.PEPS.PairEffect.SourceInventory.common_ofSlots_expands
#print axioms TNLean.PEPS.PairEffect.SourceInventory.exists_common_expansions
#print axioms TNLean.PEPS.PairEffect.SourceInventory.exists_prepareSlots_recovery
#print axioms TNLean.PEPS.PairEffect.Word.exists_common_source_preparation
#print axioms TNLean.PEPS.PairEffect.Word.exists_common_prepared_tensorPartyMaps
#print axioms TNLean.PEPS.PairEffect.Word.exists_common_source_gate
#print axioms TNLean.PEPS.PairEffect.PairSource.exists_finite_coordinates
#print axioms TNLean.PEPS.PairEffect.SourceInventory.ofSlots_mapIsometry_expands
#print axioms TNLean.PEPS.PairEffect.SourceInventory.exists_finite_coordinate_expansions
#print axioms TNLean.PEPS.PairEffect.Word.exists_finite_source_preparation
#print axioms TNLean.PEPS.PairEffect.Word.exists_finite_prepared_tensorPartyMaps
#print axioms TNLean.PEPS.PairEffect.Word.exists_finite_source_gate

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-common-source"
  IO.FS.writeFile (directory / "final-verification-20261007" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
