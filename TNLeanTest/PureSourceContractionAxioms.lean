/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.PurePreparedContraction
import TNLean.PEPS.Approximation.PurePhysicalCoefficient
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom guard for finite prepared source contractions

The product source matrix, finite column contraction, prepared pure-input
contraction and physical coefficient identity may depend only on the standard
logical axioms. Each declaration must be present in its production module.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.SourceInventory.productSourceMatrix,
      ``TNLean.PEPS.PairEffect.SourceInventory.sourceContraction_columns_eq_mul,
      ``TNLean.PEPS.PairEffect.Word.sourceContraction_preparedDensityCoefficient_pure_eq_mul,
      ``TNLean.PEPS.PairEffect.Word.preparedDensityCoefficient_pure_partialTrace_apply] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
