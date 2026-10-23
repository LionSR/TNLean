/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.Doubling
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of the doubling iteration of Hastings' area-law proof. -/

open TNLean.MPS.AreaLaw.Hastings

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``doublingStartLength_pos, ``sum_exp_le, ``sum_const_le,
      ``le_of_doubling, ``lt_of_doubling] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
