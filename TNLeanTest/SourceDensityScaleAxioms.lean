/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceDensityScale
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of the rounded density bound -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.eventually_principalDensity_le_rpow,
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.exists_principalDensity_le_rpow,
    ``TNLean.PEPS.AreaLaw.Scan.final_principalDensity_margins,
    ``TNLean.PEPS.AreaLaw.Scan.exists_final_principalDensity_le_rpow]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
