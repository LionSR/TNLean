/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.SafeRectangleAreaLaw
import Lean.Util.CollectAxioms

/-! # Logical dependencies of the real-clearance safe-rectangle estimates -/

run_cmd do
  let env ← Lean.getEnv
  let declarations : Array Lean.Name := #[
    `TNLean.PEPS.AreaLaw.card_edgeBoundary_rectRegion_le_of_disjoint,
    `TNLean.PEPS.AreaLaw.exists_regionalEntropy_safe_rect_le_linear,
    `TNLean.PEPS.AreaLaw.exists_initialBuffer_and_real_boxEntropy_recurrence
  ]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in declarations do
    match env.find? decl with
    | some (.thmInfo _) => pure ()
    | some _ => throwError "The intended declaration is not a theorem: {decl}"
    | none => throwError "The intended theorem is absent: {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Nonstandard logical dependencies for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
