/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.ConstantRankCut
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and allowed-axiom checks for constant rank across one cut. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.constantCutBond,
    ``TNLean.MPS.AreaLaw.inner_normalized_chainTrim,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.one_sub_le_re_inner_chainTrim,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_normalized_chainTrim_le,
    ``TNLean.MPS.AreaLaw.norm_normalized_chainTrim_eq_one,
    ``Matrix.IsGappedGroundState.posSemidef_sub_smul_one,
    ``TNLean.MPS.AreaLaw.re_inner_normalized_chainTrim_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.re_inner_normalized_chainTrim_le,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.exists_rank_cutMatrix_le_constantCutBond]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
