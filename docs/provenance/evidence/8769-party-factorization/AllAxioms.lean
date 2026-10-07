/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PreparedPartyMaps

/-!
# Imported axiom audit for finite party factorization

This audit checks every explicit public declaration in the seven new modules.
-/

set_option linter.hashCommand false

#print axioms TNLean.PEPS.PairEffect.Layout.restrict
#print axioms TNLean.PEPS.PairEffect.Layout.restrict_nil
#print axioms TNLean.PEPS.PairEffect.Layout.restrict_cons
#print axioms TNLean.PEPS.PairEffect.Layout.restrict_append
#print axioms TNLean.PEPS.PairEffect.Layout.restrict_eq_self_of_owner
#print axioms TNLean.PEPS.PairEffect.Layout.restrict_eq_nil_of_owner
#print axioms TNLean.PEPS.PairEffect.Layout.memCongr
#print axioms TNLean.PEPS.PairEffect.Layout.memCongr_rfl
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_cons_true
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_cons_false
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_cons_true_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_cons_false_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_append_true_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_append_false_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_cons_cons_true_true_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_cons_cons_true_false_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_cons_cons_false_true_tmul
#print axioms TNLean.PEPS.PairEffect.Layout.partitionIso_cons_cons_false_false_tmul
#print axioms TNLean.PEPS.PairEffect.Word.castLayouts
#print axioms TNLean.PEPS.PairEffect.Word.sources_castLayouts
#print axioms TNLean.PEPS.PairEffect.Word.isAllowed_castLayouts
#print axioms TNLean.PEPS.PairEffect.Word.eval_castLayouts_heq
#print axioms TNLean.PEPS.PairEffect.Word.eval_castLayouts
#print axioms TNLean.PEPS.PairEffect.Word.restrict
#print axioms TNLean.PEPS.PairEffect.Word.sources_restrict
#print axioms TNLean.PEPS.PairEffect.Word.isAllowed_restrict
#print axioms TNLean.PEPS.PairEffect.Word.restrict_localMap_true_eval_heq
#print axioms TNLean.PEPS.PairEffect.Word.restrict_localMap_false_eval_heq
#print axioms TNLean.PEPS.PairEffect.Word.restrict_swap_true_true_eval_heq
#print axioms TNLean.PEPS.PairEffect.Word.restrict_swap_true_false_eval_heq
#print axioms TNLean.PEPS.PairEffect.Word.restrict_swap_false_true_eval_heq
#print axioms TNLean.PEPS.PairEffect.Word.restrict_swap_false_false_eval_heq
#print axioms TNLean.PEPS.PairEffect.Word.restrict_frame_true_eval_heq
#print axioms TNLean.PEPS.PairEffect.Word.restrict_frame_false_eval_heq
#print axioms TNLean.PEPS.PairEffect.Word.parties
#print axioms TNLean.PEPS.PairEffect.Word.parties_castLayouts
#print axioms TNLean.PEPS.PairEffect.Word.owners_mem_parties
#print axioms TNLean.PEPS.PairEffect.Word.parties_restrict
#print axioms TNLean.PEPS.PairEffect.Word.eq_nil_and_eval_eq_id_of_parties_eq_empty
#print axioms TNLean.PEPS.PairEffect.Word.partitionIso_eval
#print axioms TNLean.PEPS.PairEffect.Layout.atParty
#print axioms TNLean.PEPS.PairEffect.partyLayout
#print axioms TNLean.PEPS.PairEffect.tensorPartyMaps
#print axioms TNLean.PEPS.PairEffect.tensorPartyMaps_cons_tmul
#print axioms TNLean.PEPS.PairEffect.partyLayout_eq_of_atParty_eq
#print axioms TNLean.PEPS.PairEffect.tensorPartyMaps_heq
#print axioms TNLean.PEPS.PairEffect.Layout.conj_memCongr_heq
#print axioms TNLean.PEPS.PairEffect.Layout.norm_conj_memCongr
#print axioms TNLean.PEPS.PairEffect.Layout.eq_conj_memCongr_of_heq
#print axioms TNLean.PEPS.PairEffect.norm_tensorPartyMaps_le_one
#print axioms TNLean.PEPS.PairEffect.Layout.withoutParty
#print axioms TNLean.PEPS.PairEffect.Layout.atParty_withoutParty
#print axioms TNLean.PEPS.PairEffect.Layout.mem_withoutParty
#print axioms TNLean.PEPS.PairEffect.Layout.owners_withoutParty
#print axioms TNLean.PEPS.PairEffect.partyLayout_withoutParty
#print axioms TNLean.PEPS.PairEffect.groupByPartyIso
#print axioms TNLean.PEPS.PairEffect.groupByPartyIso_cons
#print axioms TNLean.PEPS.PairEffect.Word.exists_tensorPartyMaps
#print axioms TNLean.PEPS.PairEffect.Word.exists_tensorPartyMaps_parties
#print axioms TNLean.PEPS.PairEffect.Word.exists_prepared_tensorPartyMaps

run_cmd do
  let environment ← Lean.getEnv
  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  let directory : System.FilePath := "/tmp/tnlean-party-factorization"
  IO.FS.writeFile (directory / "final-verification-20261007" / "imported-modules.json")
    (Lean.Json.compress (Lean.Json.arr names))
