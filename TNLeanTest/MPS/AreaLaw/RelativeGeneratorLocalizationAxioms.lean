/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.RelativeGeneratorLocalization

/-!
# Axiom check for localization of the relative-evolution generator

The termwise localization estimate uses only the three standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.ChainHamiltonian.norm_relativeGenerator_sub_siteExpectation_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  TNLean.MPS.AreaLaw.ChainHamiltonian.norm_relativeGenerator_sub_siteExpectation_le
