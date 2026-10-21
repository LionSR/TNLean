/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.CutMatrixGrowth
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and allowed-axiom checks for the four cut-rank growth estimates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_add_le,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_le_add,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_le_pow_min_mul,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_le_pow_forty_mul]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
