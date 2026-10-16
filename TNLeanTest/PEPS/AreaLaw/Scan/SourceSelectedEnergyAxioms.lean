/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedEnergy
import Lean.Util.CollectAxioms

/-!
# Logical dependencies for the general physical selected-energy estimate

The named theorem may depend only on the three standard logical axioms.
-/

run_cmd do
  let decl :=
    ``TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_sourceTarget_selected_actualCharge_source_density_energy
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "The intended source-energy theorem is absent."
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected logical dependencies: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
