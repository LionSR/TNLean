/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.SingleClusterBound
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the single-cluster bound of Hastings' cluster
expansion and the monotonicity of the trace of the exponential. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``Matrix.IsHermitian.re_trace_exp_eq_sum,
    ``Matrix.IsHermitian.re_trace_exp_le,
    ``Matrix.exp_add_smul_one,
    ``Matrix.IsHermitian.re_trace_exp_add_le,
    ``TNLean.Lattice.ClusterExpansion.norm_trace_mul_exp_sub_le,
    ``TNLean.Lattice.ClusterExpansion.inv_mul_norm_trace_mul_exp_sub_sum_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
