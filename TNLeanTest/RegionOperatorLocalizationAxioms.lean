/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegionOperatorLocalization
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit arbitrary-region localization and its two commutator identities. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``norm_commutator_le, ``norm_exp_commutator_eq,
    ``TNLean.PEPS.AreaLaw.exists_quasilocal_region_localization,
    ``TNLean.PEPS.AreaLaw.quasilocal_region_localization]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
