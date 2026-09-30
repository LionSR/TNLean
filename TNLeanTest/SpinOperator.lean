/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.SpinHalf
import TNLean.MPS.Examples.SpinOne

/-! Regression tests for exchange interactions at coincident sites. -/

open MPSTensor

example {N : ℕ} (j : Fin N) :
    spinExchange spinHalfOperator j j = (3 / 4 : ℂ) • LinearMap.id :=
  spinExchange_self _ spinHalfOperator_sum_mul_self j

example {N : ℕ} (j : Fin N) :
    spinExchange spinOneOperator j j = (2 : ℂ) • LinearMap.id :=
  spinExchange_self _ spinOneOperator_sum_mul_self j
