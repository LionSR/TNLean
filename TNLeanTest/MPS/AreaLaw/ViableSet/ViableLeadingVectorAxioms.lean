/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ViableLeadingVector
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom check for the viable leading-vector construction. -/

open TNLean.MPS.AreaLaw

run_cmd do
  let decl := ``ChainHamiltonian.exists_boundary_minimizer_leading_vector_of_isViable
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
