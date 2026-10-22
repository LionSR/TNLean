/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SupportedCutRank
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the cut rank under supported operators. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``Matrix.schmidtCoeffMatrix_kronecker_one_mulVec,
    ``TNLean.MPS.AreaLaw.rank_schmidtCoeffMatrix_mulVec_le_of_isOneSided,
    ``TNLean.MPS.AreaLaw.cutMatrix_toEuclideanLin,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_toEuclideanLin_le_of_isOneSided,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_toEuclideanLin_le_of_subset_leftBlock,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_toEuclideanLin_le_of_disjoint_leftBlock,
    ``TNLean.MPS.AreaLaw.rank_cutMatrix_toEuclideanLin_le_pow] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
