/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolRetiredAuxiliary
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom audits for the actual retired auxiliary frames

The four declarations retain the actual right and positive-stage left auxiliary
frames and their original copy labels.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.rightRetiredAuxiliary,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftRetiredAuxiliary,
      ``TNLean.MPS.AreaLaw.ChainSweep.rightRetiredAuxiliary_eq_raw,
      ``TNLean.MPS.AreaLaw.ChainSweep.leftRetiredAuxiliary_eq_raw] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
