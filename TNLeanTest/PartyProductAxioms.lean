/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyProductConjugation
import TNLean.PEPS.Approximation.PartyProductScalar
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Axiom guard for party products and private traces

The adjoint, mixed product, private partial trace and one-party scalar
identities may depend only on the standard logical axioms. The guard checks
the named declarations in their defining modules.
-/

set_option linter.hashCommand false

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``TNLean.PEPS.PairEffect.partyProductMatrix_conjTranspose,
      ``TNLean.PEPS.PairEffect.partyProductMatrix_conjugate,
      ``TNLean.PEPS.PairEffect.partialTraceRight_partyProductMatrix,
      ``TNLean.PEPS.PairEffect.partialTraceRight_partyProduct_conjugate,
      ``TNLean.PEPS.PairEffect.partyProductMatrix_smul_at_party] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
