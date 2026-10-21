/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.MPSApproximation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audits for the internal-cut rank criterion, its all-cuts corollary,
scalar multiplication, and the matrix product state approximation theorem. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.isOpenMPS_of_internal_cutMatrix_rank_le,
      ``TNLean.MPS.AreaLaw.isOpenMPS_of_cutMatrix_rank_le,
      ``TNLean.MPS.AreaLaw.IsOpenMPS.smul,
      ``TNLean.MPS.AreaLaw.exists_isOpenMPS_norm_sub_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
