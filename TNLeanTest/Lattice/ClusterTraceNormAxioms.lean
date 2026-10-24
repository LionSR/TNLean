/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.TraceNorm
import TNLean.Lattice.ClusterExpansion.AllTemperatures
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the trace-norm form of the cluster-expansion bound and
the matrix product form at every temperature in Hastings' high-temperature expansion. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.ClusterExpansion.l2OpNorm_le_one_of_mem_unitaryGroup,
    ``TNLean.Lattice.ClusterExpansion.re_trace_sqrt_le_of_forall_norm_trace_mul_le,
    ``TNLean.Lattice.ClusterExpansion.re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le,
    ``TNLean.Lattice.ClusterExpansion.posSemidef_pow_two_mul,
    ``TNLean.Lattice.ClusterExpansion.posSemidef_pow_of_even,
    ``TNLean.Lattice.ClusterExpansion.HasProductForm.pow_of_even,
    ``TNLean.Lattice.ClusterExpansion.exists_even_div_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
