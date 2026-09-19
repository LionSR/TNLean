/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.AnomalousCondensationZ2Z2Unitary

/-! Regression tests for the input-phase convention, short periodic rings,
and standard-axiom dependencies of the two-qubit physical operators. -/

open scoped Matrix BigOperators
open Z2Z2Condensation MPOTensor

-- At length one, the second-bit self-loop gives a minus sign before both flips.
example : mpo (symTensor 3) 1 (fun _ ↦ 2) (fun _ ↦ 1) = -1 := by
  rw [mpo_symTensor_apply]
  simp [physicalShift, gmul, secondCZExponent, pow_succ]

-- At length three the three second-qubit edges also give a minus sign.
example : mpo (symTensor 3) 3 (fun _ ↦ 2) (fun _ ↦ 1) = -1 := by
  rw [mpo_symTensor_apply]
  simp [physicalShift, gmul, secondCZExponent, pow_succ]

-- Both directed cyclic edges at length two are counted, so every sign is one.
example (g : Fin 4) (t : Fin 2 → Fin 4) :
    mpo (symTensor g) 2 (physicalShift g 2 t) t = 1 := by
  rw [mpo_symTensor_apply, ite_eq_left rfl]
  simp only [secondCZExponent, Fin.sum_univ_two]
  have h0 : (0 : Fin 2) + 1 = 1 := by decide
  have h1 : (1 : Fin 2) + 1 = 0 := by decide
  rw [h0, h1]
  generalize t 0 = a
  generalize t 1 = b
  fin_cases g <;> fin_cases a <;> fin_cases b <;> norm_num

-- Odd rings remain unitary, although the diagonal group element squares to -I.
example : mpo (symTensor 3) 1 ∈ Matrix.unitaryGroup (Fin 1 → Fin 4) ℂ :=
  mpo_symTensor_mem_unitaryGroup 3

example : (mpo (symTensor 3) 1)⁻¹ = -mpo (symTensor 3) 1 := by
  rw [mpo_symTensor_inv]
  simp [fusionSign]

-- The bond-two empty trace is two, not a positive-length unitary kernel.
example : mpo (symTensor 3) 0 (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) = 2 := by
  rw [mpo_apply, mpoMatrixEntry, MPOTensor.evalWord_ofFn]
  rw [List.ofFn_zero, List.prod_nil, Matrix.trace_one]
  norm_num [bondDim]

-- The inverse sign is exactly the bit-coordinate formula from the physical derivation.
example {N : ℕ} [NeZero N] (g : Fin 4) :
    (mpo (symTensor g) N)⁻¹ =
      (-1 : ℂ) ^ (((g.val / 2) * (g.val % 2)) * N) • mpo (symTensor g) N := by
  rw [mpo_symTensor_inv, fusionSign_self_eq, ← pow_mul]

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'Z2Z2Condensation.symTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.symTensor_apply

/-- info: 'Z2Z2Condensation.mpo_symTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.mpo_symTensor_apply

/-- info: 'Z2Z2Condensation.mpo_symTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.mpo_symTensor

/-- info: 'Z2Z2Condensation.mpo_symTensor_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.mpo_symTensor_mulVec_single

/-- info: 'Z2Z2Condensation.mpo_symTensor_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.mpo_symTensor_mem_unitaryGroup

/-- info: 'Z2Z2Condensation.symTensor_isMPUPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.symTensor_isMPUPos

/-- info: 'Z2Z2Condensation.mpo_symTensor_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.mpo_symTensor_zero

/-- info: 'Z2Z2Condensation.mpo_symTensor_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.mpo_symTensor_mul_self

/-- info: 'Z2Z2Condensation.fusionSign_self_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.fusionSign_self_eq

/-- info: 'Z2Z2Condensation.mpo_symTensor_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.mpo_symTensor_inv

/-- info: 'Z2Z2Condensation.mpo_symTensor_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z2Z2Condensation.mpo_symTensor_conjTranspose

end AxiomChecks
