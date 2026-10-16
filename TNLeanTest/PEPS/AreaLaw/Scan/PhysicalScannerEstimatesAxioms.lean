/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalTemplateInformation
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedSharpDensity
import TNLean.PEPS.AreaLaw.Scan.SourceTargetSharpUpper
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Standard-axiom checks for the physical sharp and rough scanner estimates. -/

open TNLean.PEPS.AreaLaw.Scan

run_cmd do
  let declarations := #[
    ``CollarScan.eventually_actualCharge_suppliedPrevector_sharp_comparison,
    ``CollarScan.eventually_actualScan_suppliedPrevector_sharp_upper,
    ``CollarScan.exists_truncated_target_actualSharpUpper,
    ``exists_finalSharp_transport_smallness,
    ``CollarScan.exists_sourceTarget_selected_actualCharge_rough_comparison,
    ``CollarScan.exists_sourceBootstrap_entropy_improvement,
    ``CollarScan.exists_sourceTarget_selected_actualCharge_sharp_comparison,
    ``exists_uniform_boxEntropy_improvement,
    ``exists_boxEntropy_le_boxError,
    ``CollarScan.exists_sourceTarget_selected_actualCharge_sharp_energy,
    ``CollarScan.exists_sourceTarget_selected_actualCharge_sharp_density,
    ``CollarScan.exists_sourceTarget_actual_mutualInformation_bound,
    ``exists_template_final_mutualInformation]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
