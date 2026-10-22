/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.ProjectorOverlap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the overlap step of Hastings' bootstrap lemma. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.toEuclideanLin_rankOneProjection,
    ``TNLean.MPS.AreaLaw.Hastings.norm_sq_sub_normSq_inner_eq,
    ``TNLean.MPS.AreaLaw.Hastings.norm_toEuclideanLin_le,
    ``TNLean.MPS.AreaLaw.Hastings.overlap_ge_of_norm_sub_rankOneProjection_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
