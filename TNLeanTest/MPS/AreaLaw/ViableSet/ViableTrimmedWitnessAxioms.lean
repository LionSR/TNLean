/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ViableTrimmedWitness
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Permitted-axiom check for the viable trimmed witness with the library bond bound. -/

run_cmd do
  let decl := ``TNLean.MPS.AreaLaw.ChainHamiltonian.exists_trimmed_witness_of_isViable
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
