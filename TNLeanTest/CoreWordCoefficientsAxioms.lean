/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.CoreWordCoefficients
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of ordered affine-product coefficients -/

run_cmd do
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.coreWordCoeff, ``Matrix.prod_coreStep_eq_sum] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
