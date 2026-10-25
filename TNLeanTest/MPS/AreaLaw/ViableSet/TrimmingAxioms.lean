/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Trimming
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and allowed-axiom checks for trimming a chain vector across one cut. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.chainTrim,
    ``TNLean.MPS.AreaLaw.cutMatrix_chainTrim,
    ``TNLean.MPS.AreaLaw.cutVector_chainTrim,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_chainTrim_self_le,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_chainTrim_le,
    ``TNLean.MPS.AreaLaw.norm_chainTrim_le,
    ``TNLean.MPS.AreaLaw.norm_inner_sub_chainTrim_le]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
