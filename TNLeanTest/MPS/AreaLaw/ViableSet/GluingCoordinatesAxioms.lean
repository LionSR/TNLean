/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.GluingCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Check the left-block coordinate declarations and their reliance on the standard axioms. -/

open TNLean.MPS.AreaLaw

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``card_cutSite_le, ``gluingLeftCoordinates, ``gluingLeftCoordinates_rightApply,
      ``gluingLeftCoordinates_spanProjection_eq_iff] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
