/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceActualInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Exact declarations and kernel dependencies of actual source information -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``TNLean.PEPS.AreaLaw.Scan.sharpInformationBound,
    ``TNLean.PEPS.AreaLaw.Scan.two_information_le_sharpInformationBound,
    ``TNLean.PEPS.AreaLaw.Scan.information_le_of_eventually_sharpInformationBound,
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_sourceTarget_actual_mutualInformation_bound]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-! The actual information bound at the named truncation constant -/

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan.CollarScan in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``sourceTarget_actual_mutualInformation_bound_explicit]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
