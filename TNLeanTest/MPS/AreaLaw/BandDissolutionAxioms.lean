/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.BandDissolution
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Presence and axiom audits for the conditional one-band construction

The six endpoint, information-environment, birth and conditional circuit declarations are
present, and their proofs use only the permitted standard axioms.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.OneBand.main₈_eq_changeOwner,
      ``TNLean.MPS.AreaLaw.OneBand.aux₄_eq_raw,
      ``TNLean.MPS.AreaLaw.OneBand.exchange_regions,
      ``TNLean.MPS.AreaLaw.OneBand.birth_liftOne,
      ``TNLean.MPS.AreaLaw.OneBand.circuits_of_primitive_information,
      ``TNLean.MPS.AreaLaw.OneBand.boundary_change_of_primitive_information] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
