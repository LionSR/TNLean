/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.RenyiObstruction
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Axiom audit for the Rényi entropy obstruction to efficient approximation. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``TNLean.MPS.AreaLaw.IsEfficientlyApproximableByMPS.exists_logarithmic_renyi_bound,
    ``TNLean.MPS.AreaLaw.not_isEfficientlyApproximableByMPS_of_superlogarithmic_renyi,
    ``TNLean.MPS.AreaLaw.not_isEfficientlyApproximableByMPS_of_renyi_power_growth]
  for decl in decls do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
