/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceFrameMatrix
import TNLean.PEPS.Approximation.SourcePairIndex

/-!
# Imported axiom audit for joint source-input contraction and pair indexing

This audit checks every explicit public declaration in the five new modules.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.SourceInventory.slotBasis
#print axioms TNLean.PEPS.PairEffect.SourceInventory.slotBasis_apply
#print axioms TNLean.PEPS.PairEffect.SourceInventory.preparedInputBasis
#print axioms TNLean.PEPS.PairEffect.SourceInventory.preparedInputBasis_apply
#print axioms TNLean.PEPS.PairEffect.Word.freeSourceMatrix
#print axioms TNLean.PEPS.PairEffect.Word.freeSourceMatrix_apply
#print axioms TNLean.PEPS.PairEffect.Word.norm_freeSourceMatrix_le_one
#print axioms TNLean.PEPS.PairEffect.Word.freeSourceMatrix_conjTranspose_mul_apply
#print axioms TNLean.PEPS.PairEffect.Word.norm_freeSourceMatrix_conjTranspose_mul_le_one
#print axioms TNLean.PEPS.PairEffect.Word.trace_preparedMatrix_mul_conjTranspose_eq
#print axioms TNLean.PEPS.PairEffect.Word.trace_preparedDensityCoefficient_eq_freeSourceMatrix
#print axioms TNLean.PEPS.PairEffect.SourceInventory.pairIndexEquiv
#print axioms TNLean.PEPS.PairEffect.SourceInventory.pairIndexEquiv_apply
#print axioms TNLean.PEPS.PairEffect.SourceInventory.length_eq_choose
#print axioms TNLean.PEPS.PairEffect.SourceInventory.length_le_card_sq
#print axioms TNLean.PEPS.PairEffect.Word.mapSourceSlots
#print axioms TNLean.PEPS.PairEffect.Word.mapSourceSlots_spec
#print axioms TNLean.PEPS.PairEffect.Word.eval_mapSourceSlots_prepareSlots
#print axioms TNLean.PEPS.PairEffect.Word.sourceFrameMatrix
#print axioms TNLean.PEPS.PairEffect.Word.sourceFrameMatrix_eq_freeSourceMatrix
#print axioms TNLean.PEPS.PairEffect.Word.norm_sourceFrameMatrix_le_one

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-source-block-contraction"
  IO.FS.writeFile (directory / "final-verification-20261007" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
