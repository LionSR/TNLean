/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolTerminalWord
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audits for the constructed private terminal word, its resource properties,
and its evaluation on arbitrary input vectors. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.terminalRegroupingWord,
      ``TNLean.MPS.AreaLaw.ChainSweep.terminalRegroupingWord_props,
      ``TNLean.MPS.AreaLaw.ChainSweep.eval_terminalRegroupingWord] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
