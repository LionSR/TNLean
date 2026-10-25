/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SourceSampleCount
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for the count and averaging of original pair samples -/

set_option linter.hashCommand false

open TNLean.Lattice.PartyCircuit.SourceCircuit

run_cmd do
  let decls := #[``length_allSourceSlots_eq_sum_pairSampleLabels,
    ``inv_sampleSize_pow_allSourceSlots_eq_prod]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
