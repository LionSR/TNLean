/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.NoneResidualOperations
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guards for scalar composition and framing

Both scalar restriction identities must exist in the production module and
depend only on the standard logical axioms.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.Word.restrict_localPart_comp_scalar,
      ``TNLean.PEPS.PairEffect.Word.restrict_localPart_frame_scalar] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
