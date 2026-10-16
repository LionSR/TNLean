/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SuppliedTargetNormAttachment
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the supplied-state norm comparisons

The named norm comparisons use only the three standard logical axioms.
-/

run_cmd do
  let decl :=
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_suppliedTarget_actualCharge_norm_bounds
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
    throwError "Unexpected logical dependencies for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
