/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.CollectiveTrimming
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and allowed-axiom checks for collective trimming of a viable subspace on the
chain. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[
    ``TNLean.MPS.AreaLaw.blockSplit,
    ``TNLean.MPS.AreaLaw.blockSplit_apply,
    ``TNLean.MPS.AreaLaw.leftSupportSubmodule_eq_comap,
    ``TNLean.MPS.AreaLaw.isCloseTo_leftSupportSubmodule_iff,
    ``TNLean.MPS.AreaLaw.blockCut,
    ``TNLean.MPS.AreaLaw.mem_blockCut,
    ``TNLean.MPS.AreaLaw.blockCut_mono,
    ``TNLean.MPS.AreaLaw.blockCutSubtypeEquiv,
    ``TNLean.MPS.AreaLaw.blockRestSubtypeEquiv,
    ``TNLean.MPS.AreaLaw.rank_cutEnvVector_blockSplit,
    ``TNLean.MPS.AreaLaw.chainTrimVector,
    ``TNLean.MPS.AreaLaw.chainTrimSubspace,
    ``TNLean.MPS.AreaLaw.chainTrimSubspace_eq_span,
    ``TNLean.MPS.AreaLaw.isCloseTo_leftSupportSubmodule_chainTrimSubspace,
    ``TNLean.MPS.AreaLaw.schmidtRank_cutVector_chainTrimVector_le]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
