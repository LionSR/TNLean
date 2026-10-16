/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.FinalSharpTransportSmallness
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of final sharp absorption -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.finalSharp_neg_log_mass_le,
    ``TNLean.PEPS.AreaLaw.Scan.finalSharp_binEntropy_le,
    ``TNLean.PEPS.AreaLaw.Scan.finalSharp_binary_cost_le,
    ``TNLean.PEPS.AreaLaw.Scan.ScannerExponents.eventually_bandCount_le_rpow,
    ``TNLean.PEPS.AreaLaw.Scan.exists_finalSharp_scale_bounds,
    ``TNLean.PEPS.AreaLaw.Scan.finalSharp_traceDistance_power,
    ``TNLean.PEPS.AreaLaw.Scan.finalSharpError,
    ``TNLean.PEPS.AreaLaw.Scan.finalSharpPowerEnvelope,
    ``TNLean.PEPS.AreaLaw.Scan.finalSharp_source_entropy_bounds,
    ``TNLean.PEPS.AreaLaw.Scan.finalSharpError_le_powerEnvelope,
    ``TNLean.PEPS.AreaLaw.Scan.finalSharp_error_exponents,
    ``TNLean.PEPS.AreaLaw.Scan.eventually_finalSharp_log_cost_le,
    ``TNLean.PEPS.AreaLaw.Scan.eventually_finalSharp_powerEnvelope_le,
    ``TNLean.PEPS.AreaLaw.Scan.exists_finalSharp_error_le,
    ``TNLean.PEPS.AreaLaw.Scan.exists_finalSharp_source_error_le,
    ``TNLean.PEPS.AreaLaw.Scan.exists_finalSharp_transport_smallness]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
