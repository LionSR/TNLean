/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairEffectSourcePreparation

/-!
# Imported axiom audit for pair-source preparation

Every explicitly public declaration from the five new modules is checked below.
The final command records the actual imported module names for artifact hashes.
-/

#print axioms TNLean.PEPS.PairEffect.appendIso_symm_cons_tmul
#print axioms TNLean.PEPS.PairEffect.Word.moveHead
#print axioms TNLean.PEPS.PairEffect.Word.isAllowed_moveHead
#print axioms TNLean.PEPS.PairEffect.Word.eval_moveHead_appendIso_symm
#print axioms TNLean.PEPS.PairEffect.Word.exchangeBlocks
#print axioms TNLean.PEPS.PairEffect.Word.isAllowed_exchangeBlocks
#print axioms TNLean.PEPS.PairEffect.Word.eval_exchangeBlocks_appendIso_symm
#print axioms TNLean.PEPS.PairEffect.PairSource
#print axioms TNLean.PEPS.PairEffect.PairSource.layout
#print axioms TNLean.PEPS.PairEffect.SourceInventory
#print axioms TNLean.PEPS.PairEffect.SourceInventory.layout
#print axioms TNLean.PEPS.PairEffect.SourceInventory.IsNormalized
#print axioms TNLean.PEPS.PairEffect.SourceInventory.prepare
#print axioms TNLean.PEPS.PairEffect.SourceInventory.layout_nil
#print axioms TNLean.PEPS.PairEffect.SourceInventory.layout_cons
#print axioms TNLean.PEPS.PairEffect.SourceInventory.layout_append
#print axioms TNLean.PEPS.PairEffect.SourceInventory.eval_frameList_prepare
#print axioms TNLean.PEPS.PairEffect.SourceInventory.eval_prepare_append
#print axioms TNLean.PEPS.PairEffect.SourceInventory.isAllowed_prepare_iff
#print axioms TNLean.PEPS.PairEffect.SourceInventory.vector
#print axioms TNLean.PEPS.PairEffect.SourceInventory.eval_prepare_eq_appendIso_symm
#print axioms TNLean.PEPS.PairEffect.SourceInventory.eval_moveHead_prepare
#print axioms TNLean.PEPS.PairEffect.Word.sources
#print axioms TNLean.PEPS.PairEffect.Word.castInput
#print axioms TNLean.PEPS.PairEffect.Word.sources_castInput
#print axioms TNLean.PEPS.PairEffect.Word.isAllowed_castInput
#print axioms TNLean.PEPS.PairEffect.Word.eval_castInput_of_heq
#print axioms TNLean.PEPS.PairEffect.Word.sources_frameList
#print axioms TNLean.PEPS.PairEffect.Word.sources_prepare
#print axioms TNLean.PEPS.PairEffect.Word.isNormalized_sources
#print axioms TNLean.PEPS.PairEffect.Word.sources_moveHead
#print axioms TNLean.PEPS.PairEffect.Word.sources_exchangeBlocks
#print axioms TNLean.PEPS.PairEffect.Word.localPart
#print axioms TNLean.PEPS.PairEffect.Word.sources_localPart
#print axioms TNLean.PEPS.PairEffect.Word.isAllowed_localPart
#print axioms TNLean.PEPS.PairEffect.Word.eval_localPart_prepare
#print axioms TNLean.PEPS.PairEffect.Word.eval_eq_localPart_comp_prepare
#print axioms TNLean.PEPS.PairEffect.expandCombinedPair
#print axioms TNLean.PEPS.PairEffect.isAllowed_expandCombinedPair
#print axioms TNLean.PEPS.PairEffect.eval_expandCombinedPair
#print axioms TNLean.PEPS.PairEffect.eval_swap_reversedSource
#print axioms TNLean.PEPS.PairEffect.PairSource.partyPair
#print axioms TNLean.PEPS.PairEffect.PairSource.reverse
#print axioms TNLean.PEPS.PairEffect.PairSource.partyPair_reverse
#print axioms TNLean.PEPS.PairEffect.PairSource.norm_reverse_vector
#print axioms TNLean.PEPS.PairEffect.PairSource.combine
#print axioms TNLean.PEPS.PairEffect.PairSource.partyPair_combine
#print axioms TNLean.PEPS.PairEffect.PairSource.norm_combine_vector
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands
#print axioms TNLean.PEPS.PairEffect.SourceInventory.isNormalized_cons
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands.refl
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands.trans
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands.cons
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands.reverse
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands.combine
#print axioms TNLean.PEPS.PairEffect.SourceInventory.Expands.swap
#print axioms TNLean.PEPS.PairEffect.SourceInventory.exists_combined
#print axioms TNLean.PEPS.PairEffect.SourceInventory.exists_grouped
#print axioms TNLean.PEPS.PairEffect.Word.exists_grouped_source_preparation
#print axioms TNLean.PEPS.PairEffect.partyPairEffectElimination_with_grouped_sources

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "/tmp/tnlean-source-preparation/final-verification-20261007/imported-modules.json"
    (Lean.Json.compress (Lean.Json.arr names))
