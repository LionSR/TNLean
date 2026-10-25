/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.VonNeumannSpectralTail
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit for the regional spectral-tail entropy bound. -/

run_cmd do
  let decl := ``TNLean.MPS.AreaLaw.regionEntropy_le_log_rank_add_spectral_tail
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
