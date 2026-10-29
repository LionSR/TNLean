/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.GaussianZeroRange
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks for exact Gaussian filtering of physical zero-range terms. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``gaussianFilteredTerm_eq_of_commute,
      ``mem_groundEigenspace_apply_of_commute,
      ``starProjection_apply_eq_of_commute,
      ``commute_of_singleton_support,
      ``commute_sum_of_singleton_support,
      ``gaussianFilteredTerm_sum_eq_of_singleton_support,
      ``singleton_support_of_zero_range,
      ``gaussianFilteredTerm_sum_eq_of_zero_range,
      ``gaussianFilteredTerm_full_and_sum_eq_of_zero_range,
      ``starProjection_term_eq_of_zero_range,
      ``sub_starProjection_gaussianFilteredTerm_sum_eq_zero_of_zero_range] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
