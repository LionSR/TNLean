/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.IncidentGateLabels
import TNLean.Lattice.Compression.PointwiseChoiceCoefficient
import TNLean.PEPS.Approximation.NetworkScalarAbsorption
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom guard for incident gate labels

The incident-label equivalences, the coefficient factorization and the vertex
scalar identity may use any subset of the three standard logical axioms. Each
declaration is checked to exist before its transitive axioms are collected, so
an absent declaration cannot pass silently.
-/

open TNLean.Lattice.PartyCircuit in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``SourceCircuit.projectAllChoices,
      ``SourceCircuit.choiceAt_projectAllChoices,
      ``SourceCircuit.choicesTouchedLabelsEquiv,
      ``SourceCircuit.choiceAt_choicesOfTouchedLabels,
      ``SourceCircuit.choicesOfTouchedLabels_choiceAt,
      ``SourceCircuit.isTouched_all_iff,
      ``SourceCircuit.allChoicesNonemptyLabelsEquiv,
      ``SourceCircuit.allChoicesNonemptyLabelsEquiv_apply,
      ``SourceCircuit.partySelector_affectedOwner_all_apply,
      ``SourceCircuit.isTouched_groupedParty_iff,
      ``SourceCircuit.choicesOfOriginalGateLabelsAt_eq_projectAllChoices,
      ``SourceCircuit.coefficient_eq_prod_dite,
      ``SourceCircuit.coefficient_all_eq_prod_nonemptyGateLocations,
      ``TNLean.PEPS.DependentBondNetwork.network_mul_at_vertex] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "{decl} depends on nonstandard axioms {axioms}"
