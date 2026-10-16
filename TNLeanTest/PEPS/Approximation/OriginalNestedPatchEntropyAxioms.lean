/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OriginalNestedPatchEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the nested-square entropy bound under the square entropy area law. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl := ``TNLean.PEPS.Approximation.SquareEntropyAreaLaw.exists_nestedPatch_entropy_le
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
