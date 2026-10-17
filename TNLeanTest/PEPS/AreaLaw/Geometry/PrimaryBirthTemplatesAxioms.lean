/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.PrimaryBirthTemplates
import Lean.Util.CollectAxioms

/-! # Logical dependencies of the primary birth templates and scanner scales -/

run_cmd do
  let ns := `TNLean.PEPS.AreaLaw.Geometry
  let names := #["primaryBirthTemplate", "primaryBirthTemplate_points",
    "card_primaryBirthTemplate_pieces_le", "exists_primaryScannerConstant",
    "primaryBirthTemplate_isSeparated", "eventually_primaryScaleLimits",
    "le_primaryScannerScale"]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    let decl := Lean.Name.str ns n
    unless (← Lean.getEnv).contains decl do
      throwError "The intended geometric declaration is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
