/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SupportedGaussianIntegral

/-!
# Axiom check for supported Gaussian averaging on a chain

The actual supported path and its Gaussian integrals use only the three
standard axioms of Lean.
-/

/--
info: 'TNLean.MPS.AreaLaw.exists_supported_gaussian_integral'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.exists_supported_gaussian_integral
