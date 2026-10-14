/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.IncidentSampledEndpointComparison
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for the separated endpoint comparisons -/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect.SourceInventory TNLean.PEPS.PairEffect.SourceCircuit

run_cmd do
  let declarations := #[
    ``endpointRegisterWord_eval_heq_of_eq,
    ``endpointDataAt,
    ``endpointRegisterData_partialSlots,
    ``restrict_endpointWord_eval_heq_selectedRegisterWord,
    ``allSourceLabel,
    ``projectedSlotChoice_eq_allSourceLabel,
    ``allPartialSlotChoice_eq_allSourceLabel,
    ``sampledEndpointOperatorLeft,
    ``sampledEndpointOperatorRight,
    ``sampledEndpointWord_eq_endpointWord,
    ``incidentSampledEndpointWord_eval_heq_endpointRegisterWord,
    ``incidentPartialSlotChoice_eq_allSourceLabel,
    ``incidentSampledEndpointWord_eval_heq_selectedRegisterWord,
    ``restrict_sampledEndpointWord_eval_heq_incidentSampledEndpointWord]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in declarations do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
