/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.QutritApproximation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the explicit qutrit tensor-power family. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := #[``TNLean.MPS.AreaLaw.EntropyScaling.norm_qutritCopies,
    ``TNLean.MPS.AreaLaw.EntropyScaling.regionEntropy_interval_qutritCopies_le,
    ``TNLean.MPS.AreaLaw.EntropyScaling.normSq_overlap_qutritFamily_le_kyFan,
    ``TNLean.MPS.AreaLaw.EntropyScaling.qutritFamily_scalar_error_lower_bound,
    ``TNLean.MPS.AreaLaw.EntropyScaling.bondDimension_qutritCopies_ge_of_scalar_error_lt_one]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
