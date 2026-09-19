/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.KramersWannierPhysical

/-!
# Regression tests for the periodic Kramers–Wannier kernel

These tests fix the output/input convention, the positive-length hypothesis,
the exceptional empty-chain trace, and annihilation of the odd spin-flip sector.
Every exported theorem of the physical-semantics leaf has an axiom guard.
-/

open KWExample
open scoped Matrix BigOperators

example (a b : Fin 0 → Fin 2) : kwTensor.mpo 0 a b = 2 :=
  kwTensor_mpo_zero a b

example (a b : Fin 1 → Fin 2) : kwTensor.mpo 1 a b = 1 := by
  rw [kwTensor_mpo_eq_prod]
  simp only [Fin.prod_univ_one]
  have hnext : (0 : Fin 1) + 1 = 0 := rfl
  rw [hnext]
  generalize a 0 = x, b 0 = y
  fin_cases x <;> fin_cases y <;> norm_num

example : kwTensor.mpo 2 ![1, 0] ![0, 1] = -1 := by
  rw [kwTensor_mpo_eq_prod]
  norm_num [Fin.prod_univ_two]

-- These length-three entries distinguish the two physical index conventions.
example : kwTensor.mpo 3 ![1, 0, 0] ![0, 1, 0] = -1 := by
  rw [kwTensor_mpo_eq_prod]
  norm_num [Fin.prod_univ_succ, Fin.add_def]

example : kwTensor.mpo 3 ![0, 1, 0] ![1, 0, 0] = 1 := by
  rw [kwTensor_mpo_eq_prod]
  norm_num [Fin.prod_univ_succ, Fin.add_def]

example {L : ℕ} [NeZero L] (v : (Fin L → Fin 2) → ℂ)
    (hv : spinFlip L *ᵥ v = -v) : kwTensor.mpo L *ᵥ v = 0 :=
  kwTensor_mpo_mulVec_eq_zero_of_odd v hv

example {L : ℕ} [NeZero L] : ¬ IsUnit (kwTensor.mpo L) :=
  kwTensor_mpo_not_isUnit

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'KWExample.kwTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_apply

/-- info: 'KWExample.kwTensor_mpo_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_mpo_eq_prod

/-- info: 'KWExample.kwTensor_mpo_eq_pow_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_mpo_eq_pow_sum

/-- info: 'KWExample.kwTensor_mpo_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_mpo_zero

/-- info: 'KWExample.flipConfig_flipConfig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.flipConfig_flipConfig

/-- info: 'KWExample.kwTensor_mpo_flip_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_mpo_flip_input

/-- info: 'KWExample.kwTensor_mpo_flip_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_mpo_flip_output

/-- info: 'KWExample.kwTensor_mpo_mul_spinFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_mpo_mul_spinFlip

/-- info: 'KWExample.spinFlip_mul_kwTensor_mpo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.spinFlip_mul_kwTensor_mpo

/-- info: 'KWExample.kwTensor_mpo_mulVec_eq_zero_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_mpo_mulVec_eq_zero_of_odd

/-- info: 'KWExample.kwTensor_mpo_not_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms KWExample.kwTensor_mpo_not_isUnit

end AxiomChecks
