/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SpectralCutoff
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the spectral cut-offs in Hastings' approximate
ground-state projector. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.MPS.AreaLaw.Hastings.isStarProjection_spectralCutoff,
    ``TNLean.MPS.AreaLaw.Hastings.norm_sub_spectralCutoff_le,
    ``TNLean.MPS.AreaLaw.Hastings.norm_mul_spectralCutoff_le,
    ``TNLean.MPS.AreaLaw.Hastings.norm_add_mul_mul_le_of_isStarProjection,
    ``TNLean.MPS.AreaLaw.Hastings.norm_add_mul_mul_spectralCutoff_le,
    ``TNLean.MPS.AreaLaw.Hastings.norm_sub_mul_le_of_isStarProjection,
    ``TNLean.MPS.AreaLaw.Hastings.spectralCutoff_localLift,
    ``TNLean.MPS.AreaLaw.Hastings.commute_spectralCutoff_localLift_of_disjoint,
    ``Entropy.IsSupportedOn.exists_localLift_isHermitian,
    ``TNLean.MPS.AreaLaw.Hastings.isSupportedOn_spectralCutoff,
    ``TNLean.MPS.AreaLaw.Hastings.commute_spectralCutoff_of_isSupportedOn] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
