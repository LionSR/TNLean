/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportedGaussianIntegral

/-! # Kernel dependencies of supported Gaussian averaging -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'QuantumCircuit.exists_supported_gaussian_integral_of_projection_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.exists_supported_gaussian_integral_of_projection_bounds
