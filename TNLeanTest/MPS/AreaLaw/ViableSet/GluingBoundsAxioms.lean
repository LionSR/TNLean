/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.GluingBounds
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom check for the bounds on every dominant chain eigenvector. -/

open TNLean.MPS.AreaLaw

run_cmd do
  let decl := ``leading_eigenvector_bounds_chain
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
