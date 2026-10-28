/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.GluingSupport
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Checks of the three standard axioms for the left support condition at the gluing cut. -/

open TNLean.MPS.AreaLaw

run_cmd do
  for decl in #[``mem_leftSupportSubmodule_of_gluingCut_fixed] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
