/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.NearestNeighbourImaginaryTime
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Permitted-axiom check for local imaginary-time conjugation. -/

run_cmd do
  let decl := ``TNLean.MPS.AreaLaw.norm_exp_conjugation_nearestNeighbour_shift_le_two
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
