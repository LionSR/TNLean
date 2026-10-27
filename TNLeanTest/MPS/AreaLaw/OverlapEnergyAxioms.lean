/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OverlapEnergy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the range-one overlap-to-energy estimates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.MPS.AreaLaw.ChainHamiltonian.re_inner_sub_le_of_overlap_of_range_one,
    ``TNLean.MPS.AreaLaw.ChainHamiltonian.re_inner_le_of_overlap_div_of_range_one] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
