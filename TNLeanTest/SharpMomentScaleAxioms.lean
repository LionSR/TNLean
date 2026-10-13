/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SharpMomentScale
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundational dependencies of the rounded marginal-moment estimates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.exists_eventually_rpow_le_mul_K,
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.sqrt_budget_le,
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.eventually_mul_a_sqrt_budget_le,
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.exists_a_le_moment_radius,
    ``TNLean.PEPS.AreaLaw.Scan.final_scanner_moment_margin,
    ``TNLean.PEPS.AreaLaw.Scan.exists_final_a_le_moment_radius]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
