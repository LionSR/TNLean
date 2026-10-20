/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.NoneResidualGate
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for the exterior restriction of an empty-party gate

The actual gate restriction identity must exist in the production module and
depend only on the standard logical axioms.
-/

set_option linter.hashCommand false

open TNLean.PEPS.PairEffect.SourceCircuit in
run_cmd do
  let decl := ``restrict_partialWord_localPart_gate_heq_coeffSum_of_isEmpty
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
