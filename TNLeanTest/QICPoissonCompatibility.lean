/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification
import TNLean.PEPS.Approximation.TwoSheetExchange
import QICLean.Probability.PoissonWordSpatialGrowth

/-!
# QICLean rectangular contraction and Poisson import compatibility

The canonical rectangular product bound must coexist with TNLean's sheet and
physical-channel consumers. The explicit matrix arguments preserve arbitrary
finite dimensions, including an empty row, intermediate, or column type.
The axiom guards cover the upstream bound, its two local matrix consumers,
and the spatial Poisson estimate consumed by the amplification development.
-/

open scoped Matrix.Norms.L2Operator

-- The rectangular contraction statement needs no decidable equality on rows.
example {r s t : Type*} [Fintype r] [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t] (A : Matrix r s ℂ) (B : Matrix s t ℂ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A * B‖ ≤ 1 :=
  Matrix.l2_opNorm_mul_le_one A B hA hB

example (A : Matrix (Fin 2) (Fin 3) ℂ) (B : Matrix (Fin 3) (Fin 5) ℂ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A * B‖ ≤ 1 :=
  Matrix.l2_opNorm_mul_le_one A B hA hB

example : ‖(0 : Matrix (Fin 0) (Fin 2) ℂ) * (0 : Matrix (Fin 2) (Fin 3) ℂ)‖ ≤ 1 :=
  Matrix.l2_opNorm_mul_le_one (0 : Matrix (Fin 0) (Fin 2) ℂ)
    (0 : Matrix (Fin 2) (Fin 3) ℂ) (by simp) (by simp)

example : ‖(0 : Matrix (Fin 2) (Fin 0) ℂ) * (0 : Matrix (Fin 0) (Fin 3) ℂ)‖ ≤ 1 :=
  Matrix.l2_opNorm_mul_le_one (0 : Matrix (Fin 2) (Fin 0) ℂ)
    (0 : Matrix (Fin 0) (Fin 3) ℂ) (by simp) (by simp)

example : ‖(0 : Matrix (Fin 2) (Fin 3) ℂ) * (0 : Matrix (Fin 3) (Fin 0) ℂ)‖ ≤ 1 :=
  Matrix.l2_opNorm_mul_le_one (0 : Matrix (Fin 2) (Fin 3) ℂ)
    (0 : Matrix (Fin 3) (Fin 0) ℂ) (by simp) (by simp)

/--
info: 'Matrix.l2_opNorm_mul_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.l2_opNorm_mul_le_one

/--
info: 'Matrix.l2_opNorm_conjTranspose_mul_mul_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.l2_opNorm_conjTranspose_mul_mul_le_one

/--
info: 'Matrix.l2_opNorm_list_prod_le_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.l2_opNorm_list_prod_le_one

/--
info: 'PoissonWord.integrable_and_integral_le_of_spatial_growth' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms PoissonWord.integrable_and_integral_le_of_spatial_growth
