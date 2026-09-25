/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.MPS.Examples.Z3Anomalous.Z3AnomalousUnitary

/-! Regression tests for the positive-length qutrit physical kernels and adjoints. -/

noncomputable section
open scoped BigOperators Matrix
open Z3Anomalous MPOTensor

-- The one-site self-loop gives the clock phase before incrementing.
example : mpo uTensor 1 (fun _ ↦ 1) (fun _ ↦ 0) = 1 := by
  rw [mpo_uTensor_apply]
  simp [funext_iff, phaseExponent, occupied]

example : mpo uTensor 1 (fun _ ↦ 2) (fun _ ↦ 1) = eisensteinOmega := by
  rw [mpo_uTensor_apply]
  simp [funext_iff, phaseExponent, occupied]

example : mpo uTensor 1 (fun _ ↦ 0) (fun _ ↦ 2) = eisensteinOmega ^ 2 := by
  rw [mpo_uTensor_apply]
  simp [funext_iff, phaseExponent, occupied]

-- The inverse phase is evaluated on the decremented configuration.
example : mpo uDagTensor 1 (fun _ ↦ 0) (fun _ ↦ 1) = 1 := by
  rw [mpo_uDagTensor_apply]
  simp [funext_iff, phaseExponent, occupied]

example : mpo uDagTensor 1 (fun _ ↦ 1) (fun _ ↦ 2) = eisensteinOmega ^ 2 := by
  rw [mpo_uDagTensor_apply]
  simp [funext_iff, phaseExponent, occupied, star_eisensteinOmega]

example : mpo uDagTensor 1 (fun _ ↦ 2) (fun _ ↦ 0) = eisensteinOmega := by
  rw [mpo_uDagTensor_apply]
  have hphase : star (eisensteinOmega ^ 2) = eisensteinOmega := by
    rw [← star_eisensteinOmega, star_star]
  simpa [funext_iff, phaseExponent, occupied, show (-1 : Fin 3) = 2 by decide]
    using hphase

-- Both directed cyclic bonds contribute on a two-site ring.
example (t : Fin 2 → Fin 3) :
    phaseExponent t =
      (occupied (t 0)).val * (t 1).val + (occupied (t 1)).val * (t 0).val := by
  simp [phaseExponent, Fin.sum_univ_two]

-- This asymmetric three-site input distinguishes the forward edge from the reverse edge.
example : mpo uTensor 3 ![1, 2, 0] ![0, 1, 2] = eisensteinOmega ^ 2 := by
  rw [mpo_uTensor_apply]
  have hshift : ![1, 2, 0] = qutritShift 3 ![0, 1, 2] := by
    funext k
    fin_cases k <;> simp
  rw [ite_eq_left hshift,
    show phaseExponent (![0, 1, 2] : Fin 3 → Fin 3) = 2 by decide +kernel]

example (L : ℕ) (hL : 0 < L) : mpo uTensor L ^ 3 = 1 := mpo_u_pow_three L hL
example (L : ℕ) (hL : 0 < L) : mpo uTensor L * mpo uDagTensor L = 1 :=
  mpo_u_mul_uDag L hL
example (L : ℕ) (hL : 0 < L) : mpo uDagTensor L * mpo uTensor L = 1 :=
  mpo_uDag_mul_u L hL

example (L : ℕ) (hL : 0 < L) : mpo uDagTensor L = (mpo uTensor L)ᴴ := by
  let : NeZero L := ⟨by omega⟩
  exact mpo_uDagTensor_eq_conjTranspose

example : IsMPUPos uTensor := uTensor_isMPUPos
example : IsMPUPos uDagTensor := uDagTensor_isMPUPos
example : mpo uTensor 0 = (2 : ℂ) • 1 := mpo_uTensor_zero
example : mpo uDagTensor 0 = (2 : ℂ) • 1 := mpo_uDagTensor_zero

section SignatureChecks

example {L : ℕ} (s : Fin L → Fin 3) (k : Fin L) :
    qutritShift L s k = s k + 1 := qutritShift_apply s k

example {L : ℕ} (s : Fin L → Fin 3) (k : Fin L) :
    (qutritShift L).symm s k = s k - 1 := qutritShift_symm_apply s k

example (i j : Fin 3) (l r : Fin 2) :
    uTensor i j l r =
      if i = j + 1 ∧ r = occupied j then eisensteinOmega ^ (l.val * j.val) else 0 :=
  uTensor_apply i j l r

example : star eisensteinOmega = eisensteinOmega ^ 2 := star_eisensteinOmega
example : star eisensteinOmega * eisensteinOmega = 1 := star_eisensteinOmega_mul
example (n : ℕ) : star (eisensteinOmega ^ n) = eisensteinOmega ^ (-(n : ℤ)) :=
  star_eisensteinOmega_pow n

variable {L : ℕ} [NeZero L]

example (s t : Fin L → Fin 3) :
    mpo uTensor L s t =
      if s = qutritShift L t then eisensteinOmega ^ phaseExponent t else 0 :=
  mpo_uTensor_apply s t

example : mpo uTensor L =
    Matrix.monomial (qutritShift L) (fun t ↦ eisensteinOmega ^ phaseExponent t) :=
  mpo_uTensor

example (t : Fin L → Fin 3) :
    mpo uTensor L *ᵥ Pi.single t 1 =
      eisensteinOmega ^ phaseExponent t • Pi.single (qutritShift L t) 1 :=
  mpo_uTensor_mulVec_single t

example : mpo uTensor L ∈ Matrix.unitaryGroup (Fin L → Fin 3) ℂ :=
  mpo_uTensor_mem_unitaryGroup

example : mpo uDagTensor L = (mpo uTensor L)ᴴ := mpo_uDagTensor_eq_conjTranspose

example : mpo uDagTensor L =
    Matrix.monomial (qutritShift L).symm
      (fun t ↦ star (eisensteinOmega ^ phaseExponent ((qutritShift L).symm t))) :=
  mpo_uDagTensor

example (s t : Fin L → Fin 3) :
    mpo uDagTensor L s t =
      if s = (qutritShift L).symm t then
        star (eisensteinOmega ^ phaseExponent ((qutritShift L).symm t)) else 0 :=
  mpo_uDagTensor_apply s t

example (s t : Fin L → Fin 3) :
    mpo uDagTensor L s t =
      if s = (qutritShift L).symm t then
        eisensteinOmega ^ (-(phaseExponent ((qutritShift L).symm t) : ℤ)) else 0 :=
  mpo_uDagTensor_apply_zpow s t

example (t : Fin L → Fin 3) :
    mpo uDagTensor L *ᵥ Pi.single t 1 =
      eisensteinOmega ^ (-(phaseExponent ((qutritShift L).symm t) : ℤ)) •
        Pi.single ((qutritShift L).symm t) 1 :=
  mpo_uDagTensor_mulVec_single t

example : mpo uDagTensor L ∈ Matrix.unitaryGroup (Fin L → Fin 3) ℂ :=
  mpo_uDagTensor_mem_unitaryGroup

example : IsMPUPos uTensor := uTensor_isMPUPos
example : IsMPUPos uDagTensor := uDagTensor_isMPUPos
example : IsMPU uTensor := uTensor_isMPU
example : IsMPU uDagTensor := uDagTensor_isMPU
example : mpo uTensor 0 = (2 : ℂ) • 1 := mpo_uTensor_zero
example : mpo uDagTensor 0 = (2 : ℂ) • 1 := mpo_uDagTensor_zero

end SignatureChecks

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'Z3Anomalous.qutritShift_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.qutritShift_apply

/-- info: 'Z3Anomalous.qutritShift_symm_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.qutritShift_symm_apply

/-- info: 'Z3Anomalous.uTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.uTensor_apply

/-- info: 'Z3Anomalous.star_eisensteinOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.star_eisensteinOmega

/-- info: 'Z3Anomalous.star_eisensteinOmega_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.star_eisensteinOmega_mul

/-- info: 'Z3Anomalous.mpo_uTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uTensor_apply

/-- info: 'Z3Anomalous.mpo_uTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uTensor

/-- info: 'Z3Anomalous.mpo_uTensor_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uTensor_mulVec_single

/-- info: 'Z3Anomalous.mpo_uTensor_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uTensor_mem_unitaryGroup

/-- info: 'Z3Anomalous.mpo_uDagTensor_eq_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uDagTensor_eq_conjTranspose

/-- info: 'Z3Anomalous.mpo_uDagTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uDagTensor

/-- info: 'Z3Anomalous.mpo_uDagTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uDagTensor_apply

/-- info: 'Z3Anomalous.star_eisensteinOmega_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.star_eisensteinOmega_pow

/-- info: 'Z3Anomalous.mpo_uDagTensor_apply_zpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uDagTensor_apply_zpow

/-- info: 'Z3Anomalous.mpo_uDagTensor_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uDagTensor_mulVec_single

/-- info: 'Z3Anomalous.mpo_uDagTensor_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uDagTensor_mem_unitaryGroup

/-- info: 'Z3Anomalous.uTensor_isMPUPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.uTensor_isMPUPos

/-- info: 'Z3Anomalous.uDagTensor_isMPUPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.uDagTensor_isMPUPos

/-- info: 'Z3Anomalous.uTensor_isMPU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.uTensor_isMPU

/-- info: 'Z3Anomalous.uDagTensor_isMPU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.uDagTensor_isMPU

/-- info: 'Z3Anomalous.mpo_uTensor_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uTensor_zero

/-- info: 'Z3Anomalous.mpo_uDagTensor_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Z3Anomalous.mpo_uDagTensor_zero

end AxiomChecks
