/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.WordOwnerRestrictionCommutation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for restriction after changing owners -/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect.Word

run_cmd do
  let decls := #[``mapOwner_castLayouts, ``restrict_mapOwner_heq]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in decls do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
