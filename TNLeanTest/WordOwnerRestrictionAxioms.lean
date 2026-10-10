/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordOwnerRestriction

/-!
# Axiom guards for source-free owner restrictions

The expected sets were copied from the actual raw reports for the two
owner-restriction identities and the single-party selector.
-/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.PairEffect.Word.parties_mapOwner_of_sources_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.PairEffect.Word.parties_mapOwner_of_sources_nil

/-- info: 'TNLean.PEPS.PairEffect.Word.restrict_mapOwner_eval_eq_id_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.PairEffect.Word.restrict_mapOwner_eval_eq_id_of_disjoint

/-- info: 'TNLean.PEPS.PairEffect.partySelector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TNLean.PEPS.PairEffect.partySelector
