/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TwoMarkerScalarRecovery
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Axiom checks for TwoMarkerScalarRecovery -/

run_cmd do
  let env ← Lean.getEnv
  let checks : Array (Lean.Name × Array Lean.Name) := #[
    (``MvPolynomial.twoMarkerOrdinaryLabels,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``WordMultiplicity.wordCoefficient,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``Polynomial.exists_twoWindow_wordCoefficient_recovery,
      #[``propext, ``Classical.choice, ``Quot.sound])
  ]
  for (decl, expected) in checks do
    unless env.contains decl do
      throwError "Missing public declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
