/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RegionalMiddleFactors
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Kernel dependencies of regional middle families -/

run_cmd do
  let env ← Lean.getEnv
  let expectations : Array (Lean.Name × Array Lean.Name) := #[
    (``TNLean.MPS.AreaLaw.exists_regional_exterior_of_natural_threeSplit_decomposition,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``FiniteProduct.changingOldMiddleConfigEquiv,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``FiniteProduct.changingNewMiddleConfigEquiv,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``FiniteProduct.changingRegionalMiddleFamily,
      #[``propext, ``Classical.choice, ``Quot.sound]),
    (``FiniteProduct.exists_changingRegional_exterior_family,
      #[``propext, ``Classical.choice, ``Quot.sound])]
  for (decl, expected) in expectations do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let actual ← Lean.collectAxioms decl
    unless actual.size == expected.size && actual.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {actual}"
