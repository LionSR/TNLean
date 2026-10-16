/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BootstrapScannerExponents
import TNLean.PEPS.AreaLaw.Scan.FixedWeightTransportSmallness
import TNLean.PEPS.AreaLaw.Scan.ScannerRoundedAdmissibility
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of the bootstrap scanner numerics -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.BootstrapParameters.scannerExponents,
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.exists_fixedWeightFour_transport_smallness,
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.exists_rounded_admissibility]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

open TNLean.PEPS.AreaLaw.Scan

example (e₀ : ℝ) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) :
    let X := BootstrapParameters.scannerExponents e₀ he₀ he₀₁
    X.ell = BootstrapParameters.ell e₀ ∧
      X.kappa = BootstrapParameters.kappa e₀ ∧
      X.mu = BootstrapParameters.mu e₀ ∧
      X.nu = BootstrapParameters.nu e₀ ∧ X.e = BootstrapParameters.mu e₀ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example (e₀ : ℝ) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) (n : ℕ) :
    let X := BootstrapParameters.scannerExponents e₀ he₀ he₀₁
    X.K n = Nat.floor ((n : ℝ) ^ (1 - BootstrapParameters.ell e₀)) /
      (8 * Nat.floor ((n : ℝ) ^ BootstrapParameters.mu e₀)) := rfl
