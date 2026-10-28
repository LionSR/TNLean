/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.NoSingletonWords
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of the count of words without singleton letters. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Finset.card_image_le_half_of_no_singleton,
      ``Fintype.exists_factor_fin_of_card_range_le,
      ``Fintype.card_functions_of_card_range_le,
      ``Fintype.card_even_words_without_singleton] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
