/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ComponentReduction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for Theorem A on a finite set of integers

The zero-entropy cut, the flip of a region of zero entropy, and Theorem A on a finite set of
integers must exist in the production module and depend only on standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.Lattice.regionEntropy_eq_zero_of_forall_subset_or_disjoint,
      ``TNLean.Lattice.regionEntropy_symmDiff_eq_of_eq_zero,
      ``TNLean.MPS.AreaLaw.card_domainBoundaryEdges,
      ``TNLean.MPS.AreaLaw.regionEntropy_le_mul_card_domainBoundaryEdges,
      ``TNLean.MPS.AreaLaw.domainAreaLaw] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
