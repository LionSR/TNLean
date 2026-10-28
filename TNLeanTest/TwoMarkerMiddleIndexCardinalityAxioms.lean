/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoMarkerMiddleIndexCardinality
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of the two-binomial crossing-word count -/

run_cmd do
  let env ← Lean.getEnv
  let decl := ``TNLean.MPS.AreaLaw.card_twoMarkerMiddleIndex_two_binomial_le
  unless env.contains decl do
    throwError "Missing public declaration {decl}"
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms decl
  unless axioms.size == expected.size && axioms.all (expected.contains ·) do
    throwError "Unexpected axioms for {decl}: {axioms}"
