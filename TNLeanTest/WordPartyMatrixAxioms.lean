/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.WordPartyMixedMatrix
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for actual party-coordinate matrices

The three coordinate theorems must exist in the production module and depend only
on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.Word.partyGroupedBasis_repr_eval,
      ``TNLean.PEPS.PairEffect.Word.partyGroupedBasis_matrix_eval,
      ``TNLean.PEPS.PairEffect.Word.partyGroupedBasis_mixed_matrix] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
