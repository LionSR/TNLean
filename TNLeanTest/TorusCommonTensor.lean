/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusCommonTensor

/-! Axiom checks for the injective PEPS translation-invariance construction. -/

set_option linter.hashCommand false

/-- info: 'TNLean.PEPS.stateCoeff_torusFourLegTensor_uniformBondAbsorption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.stateCoeff_torusFourLegTensor_uniformBondAbsorption

/-- info: 'TNLean.PEPS.exists_isTorusTranslationInvariant_sameState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.exists_isTorusTranslationInvariant_sameState
