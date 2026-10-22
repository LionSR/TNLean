/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualPureSourceReplacement
import TNLean.Lattice.Compression.ActualSampledExteriorScalar
import TNLean.Lattice.Compression.ActualSampledPhysicalFactors
import TNLean.PEPS.Approximation.DistributedPhysicalPrivateTrace
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for the original physical mixed trace and source expansion -/

set_option linter.hashCommand false

open TNLean.Lattice.PartyCircuit.SourceCircuit in
run_cmd do
  let decls := #[
    ``TNLean.Lattice.PartyCircuit.SourceCircuit.sourceReplacedDensity_pure_eq_sum_actualColumns,
    ``partialSourceWord_sampled_none_partialTrace_eq_scalar,
    ``sampledPhysicalFactor,
    ``partialSourceGlobalMatrix_sampled_partialTrace_eq_sum_physicalFactors,
    ``TNLean.Lattice.PartyCircuit.selectedPhysicalPrivateBasis_partialTrace_mixed,
    ``TNLean.Lattice.PartyCircuit.DistributedConstruction.physicalDensity_eq_grouped_partialTrace]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
