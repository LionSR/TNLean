/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapConjugateSupport
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the original support of a swapped doubled interaction. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decl :=
    ``TNLean.PEPS.EncodedFrame.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators
  unless (← Lean.getEnv).contains decl do
    throwError "Missing declaration {decl}"
  let axioms ← Lean.collectAxioms decl
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
  Lean.logInfo m!"{decl}: {axioms}"
