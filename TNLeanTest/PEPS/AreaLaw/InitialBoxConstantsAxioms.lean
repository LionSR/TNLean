/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialBoxEstimate
import Lean.Util.CollectAxioms

/-! # Logical dependencies of the initial box estimate at named constants -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``TNLean.PEPS.AreaLaw.condEntropy_le_initialBufferConst,
      ``TNLean.PEPS.AreaLaw.exists_condEntropy_le_initialBuffer,
      ``TNLean.PEPS.AreaLaw.boxEntropy_le_initialBoxRatio_mul,
      ``TNLean.PEPS.AreaLaw.initialBoxExponent_pos_and_lt_one,
      ``TNLean.PEPS.AreaLaw.boxEntropy_le_initialBoxConstant_mul_rpow_of_scaleRecurrence,
      ``TNLean.PEPS.AreaLaw.boxEntropy_le_initialBoxConstant_mul_rpow,
      ``TNLean.PEPS.AreaLaw.exists_boxEntropy_le_rpow] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
