/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ViableLeadingBounds
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Checks of the three standard axioms for the uniform viable leading bounds. -/

open TNLean.MPS.AreaLaw

run_cmd do
  for decl in #[``ChainHamiltonian.exists_uniform_leading_bounds_of_isViable] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
