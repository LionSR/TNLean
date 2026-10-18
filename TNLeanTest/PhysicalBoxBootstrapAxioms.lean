/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalBoxBootstrap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of the physical safe-box bootstrap -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
  ``TNLean.PEPS.AreaLaw.Scan.exists_bootstrap_selected_energy_bound,
  ``TNLean.PEPS.AreaLaw.Scan.exists_bootstrap_restored_entropy_budget,
  ``TNLean.PEPS.AreaLaw.regionalEntropy_le_of_boxEntropy_power,
  ``TNLean.PEPS.AreaLaw.boxEntropy_power_le_of_large_rectangles,
  ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.exists_actualCharge_energy_coefficients,
  ``TNLean.PEPS.AreaLaw.Scan.CollarScan.actualCharge_defect_le_of_density_energy_bound_at_exponent,
  ``TNLean.PEPS.AreaLaw.Scan.exists_uniform_boxEntropy_improvement,
  ``TNLean.PEPS.AreaLaw.Scan.exists_boxEntropy_le_boxError,
  ``TNLean.PEPS.AreaLaw.Scan.exists_uniform_boxEntropy_improvement_of_threshold_le,
  ``TNLean.PEPS.AreaLaw.Scan.exists_boxEntropy_le_boxError_of_initial,
  ``TNLean.PEPS.AreaLaw.Scan.weakRectangle_source_entropy_bounds,
  ``TNLean.PEPS.AreaLaw.Scan.exists_weakRectangle_source_entropy_bounds,
  ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.exists_rough_selectedDensity_principal,
  ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_sourceBootstrap_entropy_improvement,
  ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_sourceTarget_selected_actualCharge_rough_comparison]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
