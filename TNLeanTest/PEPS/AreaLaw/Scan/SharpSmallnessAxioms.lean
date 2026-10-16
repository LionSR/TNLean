/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SharpSmallness
import Lean.Util.CollectAxioms

/-! # Permitted axioms for the sharp-comparison moment radii -/

run_cmd do
  let decl := ``TNLean.PEPS.AreaLaw.Scan.sharpSmallness_le_moment_radius
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
