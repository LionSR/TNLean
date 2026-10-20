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

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.SourceCircuit.projectAllChoices,
      ``TNLean.PEPS.PairEffect.SourceCircuit.choiceAt_projectAllChoices,
      ``TNLean.PEPS.PairEffect.SourceCircuit.choicesTouchedLabelsEquiv,
      ``TNLean.PEPS.PairEffect.SourceCircuit.choiceAt_choicesOfTouchedLabels,
      ``TNLean.PEPS.PairEffect.SourceCircuit.choicesOfTouchedLabels_choiceAt,
      ``TNLean.PEPS.PairEffect.SourceCircuit.isTouched_all_iff,
      ``TNLean.PEPS.PairEffect.SourceCircuit.allChoicesNonemptyLabelsEquiv,
      ``TNLean.PEPS.PairEffect.SourceCircuit.allChoicesNonemptyLabelsEquiv_apply,
      ``TNLean.PEPS.PairEffect.SourceCircuit.partySelector_affectedOwner_all_apply,
      ``TNLean.PEPS.PairEffect.SourceCircuit.isTouched_groupedParty_iff,
      ``TNLean.PEPS.PairEffect.SourceCircuit.choicesOfOriginalGateLabelsAt_eq_projectAllChoices,
      ``TNLean.PEPS.PairEffect.SourceCircuit.coefficient_eq_prod_dite,
      ``TNLean.PEPS.PairEffect.SourceCircuit.coefficient_all_eq_prod_nonemptyGateLocations,
      ``TNLean.PEPS.DependentBondNetwork.network_mul_at_vertex] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "{decl} depends on nonstandard axioms {axioms}"
