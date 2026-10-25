/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.TailRenyiEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the Rényi entropy bound under geometric tail
constraints in Hastings' bootstrap lemma. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.sum_rpow_le_card_rpow_mul_sum_rpow,
    ``TNLean.MPS.AreaLaw.Hastings.sum_rpow_le_of_geometric_tails,
    ``TNLean.MPS.AreaLaw.Hastings.renyiEntropy_le_of_geometric_tails,
    ``TNLean.MPS.AreaLaw.Hastings.renyiEntropy_le_of_scale_tails] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
