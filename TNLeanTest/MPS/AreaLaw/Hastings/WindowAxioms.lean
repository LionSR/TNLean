/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.Window
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Logical dependencies of the entropy window of Hastings' area-law proof. -/

open TNLean.MPS.AreaLaw.Hastings

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.Lattice.regionEntropy_nonneg, ``cutEntropy_sub_le,
      ``windowLength_mul_log_le, ``lt_windowLength_add_one, ``two_mul_div_three_le_cutEntropy,
      ``regionEntropy_le_windowEntropy, ``exists_windowEntropy_eq, ``windowEntropy_nonneg,
      ``windowEntropy_le, ``windowEntropy_two_mul_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
