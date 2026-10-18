/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OwnershipChanges
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit for birth, death and two-sheet exchange with arbitrary error exponent. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.birth_bounded_rpow,
      ``TNLean.MPS.AreaLaw.death_bounded_rpow, ``TNLean.MPS.AreaLaw.exchange_bounded_rpow] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
