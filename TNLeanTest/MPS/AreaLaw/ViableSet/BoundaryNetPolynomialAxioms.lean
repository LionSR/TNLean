/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.BoundaryNetPolynomial
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the polynomial boundary-net bounds and their reliance on the standard axioms. -/

open TNLean.MPS.AreaLaw

run_cmd do
  for decl in #[``boundaryNet_card_bound_le_polynomial,
      ``exists_finset_boundary_rectangularTraceNorm_net_polynomial] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
