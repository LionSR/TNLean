/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceRoundedInformation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of automatic rounded-scale physical information -/

open TNLean.PEPS.AreaLaw.Scan
open TNLean.PEPS.AreaLaw.Scan.CollarScan

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``exists_finalScanner_admissibility,
    ``exists_sourceTarget_finalScale_mutualInformation_of_rounded_scales]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-! The rounded-scale information at the named truncation constant -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``sourceTarget_finalScale_mutualInformation_of_rounded_scales_explicit]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
