/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ProductReferenceColumn
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Fail closed unless every new theorem exists and uses only the standard
trusted Lean axioms. The collected sets are also written to the CI log. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``TNLean.PEPS.Approximation.Pinned.exists_fixInput_contractPEPS_of_product_reference,
      ``TNLean.PEPS.Approximation.Pinned.exists_peps_of_product_reference] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
