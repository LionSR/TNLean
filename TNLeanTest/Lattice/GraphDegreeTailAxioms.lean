/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GraphDegreeTail
import TNLean.Lattice.GaussianTruncationDecayBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Permitted-axiom checks for bounded-degree weighted tails -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.Lattice.card_graphClosedBall_le,
      ``TNLean.Lattice.sum_weight_anchor_le_of_support_budget,
      ``TNLean.Lattice.sum_weight_mul_comp_le_budget_mul_sum,
      ``TNLean.Lattice.sum_weight_meeting_le_card_mul_budget,
      ``TNLean.Lattice.sum_weight_meeting_graphClosedBall_le,
      ``TNLean.Lattice.graphClosedBall_subset_of_mem,
      ``TNLean.Lattice.graphClosedBall_separation,
      ``TNLean.Lattice.le_anchorDecay_of_separated_exp,
      ``TNLean.Lattice.sum_exp_neg_edist_le_degree,
      ``TNLean.Lattice.sum_weight_exp_neg_edist_tail_le_degree,
      ``TNLean.Lattice.gaussian_truncation_bound_le_exp] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
