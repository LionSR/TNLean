/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.LayoutOwnerMap
import TNLean.PEPS.Approximation.LocalPairSource
import TNLean.PEPS.Approximation.SourceOwnerMap
import TNLean.PEPS.Approximation.WordOwnerMap
import TNLean.PEPS.Approximation.PartyCoarseningFactorization

/-!
# Imported axiom audit for grouping parties and exact separated contractions

This audit checks every explicit public declaration in the five new modules.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.Layout.mapOwner
#print axioms TNLean.PEPS.PairEffect.Layout.mapOwner_nil
#print axioms TNLean.PEPS.PairEffect.Layout.mapOwner_cons
#print axioms TNLean.PEPS.PairEffect.Layout.mapOwner_append
#print axioms TNLean.PEPS.PairEffect.Layout.mapOwnerIso
#print axioms TNLean.PEPS.PairEffect.Layout.mapOwnerIso_nil_apply
#print axioms TNLean.PEPS.PairEffect.Layout.mapOwnerIso_cons_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.mapOwnerIso_append_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.mapOwnerIso_append
#print axioms TNLean.PEPS.PairEffect.PairSource.mapOwner
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mapOwner
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mapOwner_nil
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mapOwner_cons
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mapOwner_append
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mem_mapOwner
#print axioms TNLean.PEPS.PairEffect.SourceInventory.IsNormalized.mapOwner
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mapOwner_eq_nil_iff
#print axioms TNLean.PEPS.PairEffect.SourceInventory.map_partyPair_mapOwner
#print axioms TNLean.PEPS.PairEffect.SourceInventory.mem_partyPair_mapOwner
#print axioms TNLean.PEPS.PairEffect.Word.localPairSource
#print axioms TNLean.PEPS.PairEffect.Word.localPairSource_spec
#print axioms TNLean.PEPS.PairEffect.Word.eval_localPairSource
#print axioms TNLean.PEPS.PairEffect.Word.mapOwner
#print axioms TNLean.PEPS.PairEffect.Word.isAllowed_mapOwner
#print axioms TNLean.PEPS.PairEffect.Word.sources_mapOwner
#print axioms TNLean.PEPS.PairEffect.Word.eval_mapOwner
#print axioms TNLean.PEPS.PairEffect.Word.eval_mapOwner_comp
#print axioms TNLean.PEPS.PairEffect.Word.exists_partition_of_sources_internal

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-party-coarsening"
  IO.FS.writeFile (directory / "final-verification-20261007" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
