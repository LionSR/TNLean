/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PureSourceMatrix
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom guard for pure prepared source coefficients

The source-to-output matrix and its outer-product identity may depend only on
the standard logical axioms. Each declaration must be present in the imported
production module before its transitive axiom dependencies are collected.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.Word.pureSourceMatrix,
      ``TNLean.PEPS.PairEffect.Word.preparedDensityCoefficient_pure_eq_vecMulVec] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
