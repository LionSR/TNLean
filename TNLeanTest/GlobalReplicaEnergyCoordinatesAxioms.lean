/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.GlobalReplicaEnergyCoordinates
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the global replica energy and its expectation. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.Scan.copyMean_augmentOperator_eq_globalReplicaMeanHamiltonian,
      ``TNLean.PEPS.AreaLaw.Scan.star_dotProduct_copyMean_augmentOperator] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
