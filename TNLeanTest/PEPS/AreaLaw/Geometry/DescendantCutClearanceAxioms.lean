/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.DescendantCutClearance
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the cut clearance of belt and descendant templates

Each public theorem must exist and have precisely the three standard logical axioms.
-/

run_cmd do
  let ns := `TNLean.PEPS.AreaLaw.Geometry
  let names := #[`two_pow_fineScaleIndex_le_rpow, `eventually_descendant_cutClearance_scales,
    `Template.cutClearance_of_endpoint_dist_ge, `repairStage_zero_endpoint_dist_ge,
    `repairStage_birth_endpoint_dist_ge, `initialBelt_birthTemplate_cutClearance,
    `descendant_birthTemplate_cutClearance]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    let decl := ns ++ n
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric declaration is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
