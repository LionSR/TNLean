/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.AreaLawExplicitConstant
import Lean.Util.CollectAxioms

/-!
# Logical dependencies of the area law with an explicit constant

Each public declaration must exist and have precisely the three standard logical axioms.
-/

run_cmd do
  let names := #[
    `TNLean.PEPS.AreaLaw.uniformAreaLawConstantExplicit,
    `TNLean.PEPS.AreaLaw.uniformAreaLaw_explicit]
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in names do
    unless (← Lean.getEnv).contains decl do
      throwError "The intended area-law declaration is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (expected.contains ·) && expected.all (axioms.contains ·) do
      throwError "Unexpected logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
