/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationGroundSpace
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-axiom checks for translation on the actual ground eigenspace. -/

open TNLean.Lattice

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.sitePermMatrix_one, ``groundTranslation, ``groundTranslationConjugation,
      ``sitePerm_starProjection_commute, ``groundTranslation_apply_coe,
      ``groundTranslation_symm_apply, ``groundTranslationConjugation_groundSpaceCompression,
      ``groundTranslationConjugation_pow_compression_of_covariant,
      ``groundTranslationConjugation_pow_compression] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
