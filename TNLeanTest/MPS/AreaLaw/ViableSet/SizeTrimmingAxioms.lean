/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.SizeTrimming
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! The finite size-trimming construction uses only the three standard axioms. -/

run_cmd do
  for decl in #[``TNLean.MPS.AreaLaw.ChainHamiltonian.exists_size_trimmed_family,
      ``TNLean.MPS.AreaLaw.ChainHamiltonian.exists_size_trimmed_family_polynomial] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
