/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualSampledPartyContraction
import TNLean.Lattice.Compression.ActualSampledEndpointInputWord
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guards for actual sampled endpoint coordinates

The twenty-one production declarations must exist and depend only on the standard
logical axioms. The finite sampled sum retains the original joint assignment.
-/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect TNLean.Lattice.PartyCircuit.SourceCircuit
  TNLean.Lattice.PartyCircuit.SourceInventory in
run_cmd do
  let decls := #[
    ``slotVector_eq_sum_slotBasis,
    ``slotBasis_repr_slotVector,
    ``basisMatrixOperator,
    ``basisMatrixOperator_repr,
    ``matrix_repr_eval_eq_toMatrix,
    ``slotBasis_repr_endpointWord,
    ``endpointMatrixWord,
    ``slotBasis_repr_endpointMatrixWord,
    ``endpointMatrixAverage_eq_product,
    ``sampledEndpointLeft,
    ``sampledEndpointRight,
    ``sampledSourceMatrix_eq_endpoint_average,
    ``sampledEndpointWord,
    ``sources_sampledEndpointWord,
    ``sampledEndpointWord_average,
    ``sampledEndpointInputWord,
    ``sources_sampledEndpointInputWord,
    ``actualSourceInputBasis_repr_sampledEndpointInputWord,
    ``sampledEndpointInputMatrix_average,
    ``partialSourceGlobalMatrix_mixed_word,
    ``partialSourceGlobalMatrix_sampled_eq_sum_partyProduct]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
