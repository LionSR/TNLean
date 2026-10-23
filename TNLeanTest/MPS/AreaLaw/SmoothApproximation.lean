/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.SmoothApproximation

/-! # Axioms of the independently smoothed truncation estimate -/

open TNLean.MPS.AreaLaw

set_option linter.hashCommand false

/-- info: 'TNLean.MPS.AreaLaw.norm_sequentialTruncation_leadingEigenprojection_sub_sq_le_of_smoothing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_sequentialTruncation_leadingEigenprojection_sub_sq_le_of_smoothing
