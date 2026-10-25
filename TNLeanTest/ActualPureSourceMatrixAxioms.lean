/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.ActualPureSourceMatrix
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom guard for the actual pure-input source contraction

The literal source-column contraction must exist in the production module and
depend only on the standard logical axioms.
-/

set_option linter.hashCommand false

open TNLean.Lattice.PartyCircuit in
run_cmd do
  let decl :=
    ``SourceCircuit.sourceContraction_preparedDensityCoefficient_pure_eq_mul
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  unless env.contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
