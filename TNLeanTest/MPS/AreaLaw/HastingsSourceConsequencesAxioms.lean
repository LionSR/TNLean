/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SourceConsequences
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Permitted-axiom checks for the common-source-length consequences

These checks cover the von Neumann and Rényi bootstrap inequalities, the
entropy gain across a cut, and the matrix product state approximation with
the printed entropy threshold.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.exists_entropy_le_of_overlap_schmidtRank_mixture_source,
      ``TNLean.MPS.AreaLaw.exists_renyiEntropy_le_of_overlap_schmidtRank_mixture_source,
      ``TNLean.MPS.AreaLaw.exists_renyiEntropy_le_of_overlap_schmidtRank_mixture_of_one_lt_source,
      ``TNLean.MPS.AreaLaw.Hastings.exists_relent_of_isGappedGroundState_source,
      ``TNLean.MPS.AreaLaw.Hastings.exists_isOpenMPS_norm_sub_sq_le_of_isGappedGroundState_source
      ] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
