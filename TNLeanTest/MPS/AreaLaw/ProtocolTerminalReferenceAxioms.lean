/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolTerminalReference
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom checks for the constructed auxiliary reference, the actual stack/raw
label identification, its reference factorization, and the density estimate. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainSweep.auxiliaryReference_apply,
      ``TNLean.MPS.AreaLaw.ChainSweep.norm_auxiliaryReference,
      ``TNLean.MPS.AreaLaw.ChainSweep.terminalRawOrder_nodup,
      ``TNLean.MPS.AreaLaw.ChainSweep.mem_terminalRawOrder,
      ``TNLean.MPS.AreaLaw.ChainSweep.stackRegs_terminalFrames,
      ``TNLean.MPS.AreaLaw.ChainSweep.terminalStackReadout_framesVec,
      ``TNLean.MPS.AreaLaw.ChainSweep.partialTrace_terminalStackReference,
      ``TNLean.MPS.AreaLaw.ChainSweep.rectangularTraceNorm_terminalStackReadout_sub_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
