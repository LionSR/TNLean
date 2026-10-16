/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicOwnerSwitch

/-!
# Axiom checks for switching the party map between events

The comparison of the frames read through the party maps of two repaintings depends only on the
standard axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.Approximation.labelParty_eq_of_ne_guidePlaceholder,
      ``TNLean.PEPS.Approximation.guideFrame_labelParty_eq,
      ``TNLean.PEPS.Approximation.exists_isBoundedChange_labelParty_switch,
      ``TNLean.PEPS.Approximation.blockGuide_protocolLevelLabels_ne_guidePlaceholder,
      ``TNLean.PEPS.Approximation.IsDisplacedReading.ne_guidePlaceholder,
      ``TNLean.PEPS.Approximation.cellCenterPos_mem_openRoot,
      ``TNLean.PEPS.Approximation.guideFrame_levelLabels_labelParty_eq,
      ``TNLean.PEPS.Approximation.exists_isBoundedChange_levelLabels_labelParty_switch] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
