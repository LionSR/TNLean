/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TemplateFinalInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of conditional original-template information -/

open TNLean.PEPS.AreaLaw.Scan

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``finalTemplateScanner,
    ``finalTemplateScanner_truncationSet,
    ``exists_template_final_mutualInformation_of_boxEntropy]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-! The template information at the named truncation constant -/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan.CollarScan in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Scan.template_final_mutualInformation_of_boxEntropy_explicit]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
