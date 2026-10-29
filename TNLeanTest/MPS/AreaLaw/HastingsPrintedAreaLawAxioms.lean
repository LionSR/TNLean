/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.PrintedAreaLawSource
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Permitted-axiom checks for Hastings' printed entropy bound

The checks cover the entropy estimate at an enlarged length, its deduction for the
explicit source pair, and the numerical commutator bound for that pair.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.Hastings.exists_regionEntropy_prefix_le_printed,
      ``TNLean.MPS.AreaLaw.Hastings.exists_regionEntropy_prefix_le_source,
      ``TNLean.MPS.AreaLaw.ChainHamiltonian.norm_heisenberg_commutator_le_hastings_source,
      ``TNLean.MPS.AreaLaw.exists_projectorFactorization_posSemidef_source,
      ``TNLean.MPS.AreaLaw.exists_projectorFactorization_source] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
