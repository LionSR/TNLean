/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Reduction.Examples.ElementaryStates

/-!
# Signature and axiom tests for elementary state identifications

The GHZ source agrees with the standard tensor only at positive length.
The repeated source is twice the product state at all lengths, including zero.
-/

open MPSTensor
open scoped BigOperators Matrix

example (x : Fin 2) : ghzC x = ghzSectorTensor x := ghzC_eq_ghzSectorTensor x

example {N : ℕ} (x : Fin 2) (σ : Fin N → Fin 2) :
    mpv (ghzC x) σ = if ∀ n, σ n = x then 1 else 0 := ghzC_mpv x σ

example {N : ℕ} (σ : Fin N → Fin 2) :
    mpv ghzTensor σ = (if ∀ n, σ n = 0 then 1 else 0) +
      (if ∀ n, σ n = 1 then 1 else 0) := ghzTensor_mpv σ

example {N : ℕ} (hN : 0 < N) (σ : Fin N → Fin 2) :
    mpv ghzB σ = (if ∀ n, σ n = 0 then 1 else 0) +
      (if ∀ n, σ n = 1 then 1 else 0) := ghzB_mpv hN σ

example : SameMPV₂Pos ghzB ghzTensor := ghzB_sameMPV₂Pos_ghzTensor

example {N : ℕ} (hN : 0 < N) : mpvState ghzB N = mpvState ghzTensor N :=
  ghzB_mpvState_eq hN

example : ¬ SameMPV₂ ghzB ghzTensor := ghzB_not_sameMPV₂_ghzTensor

example {N : ℕ} (σ : Fin N → Fin 2) :
    mpv repA σ = ∏ n, (![1, 2] : Fin 2 → ℂ) (σ n) := repA_mpv σ

example {N : ℕ} (σ : Fin N → Fin 2) : mpv repB σ = 2 * mpv repA σ :=
  repB_mpv_eq_two_mul σ

example {N : ℕ} (σ : Fin N → Fin 2) :
    mpv repB σ = 2 * ∏ n, (![1, 2] : Fin 2 → ℂ) (σ n) := repB_mpv σ

example (N : ℕ) : mpvState repB N = (2 : ℂ) • mpvState repA N := repB_mpvState_eq N

example {N : ℕ} (hN : 0 < N) : ‖mpvState ghzB N‖ ^ 2 = 2 := ghzB_mpvState_norm_sq hN

example (N : ℕ) : ‖mpvState repA N‖ ^ 2 = 5 ^ N := repA_mpvState_norm_sq N

example (N : ℕ) : ‖mpvState repB N‖ ^ 2 = 4 * 5 ^ N := repB_mpvState_norm_sq N

-- Empty-chain amplitudes and the all-length product-state norm.
example (σ : Fin 0 → Fin 2) : mpv ghzB σ = 4 := by simp
example (σ : Fin 0 → Fin 2) : mpv ghzTensor σ = 2 := by simp
example (σ : Fin 0 → Fin 2) : mpv repB σ = 2 := by simp
example : ‖mpvState repB 0‖ ^ 2 = 4 := by norm_num [repB_mpvState_norm_sq]

-- Both GHZ sectors survive, while mixed configurations vanish.
example : mpv ghzB (fun _ : Fin 1 => 0) = 1 := by
  rw [ghzB_mpv (by decide)]
  norm_num
example : mpv ghzB (fun _ : Fin 1 => 1) = 1 := by
  rw [ghzB_mpv (by decide)]
  norm_num
example : mpv ghzB (![0, 1] : Fin 2 → Fin 2) = 0 := by
  rw [ghzB_mpv (by decide)]
  norm_num [Fin.forall_fin_two]

-- Local amplitudes multiply, with a single global factor two.
example : mpv repB (fun _ : Fin 1 => 0) = 2 := by
  rw [repB_mpv]
  norm_num
example : mpv repB (fun _ : Fin 1 => 1) = 4 := by
  rw [repB_mpv]
  norm_num
example : mpv repB (![0, 1] : Fin 2 → Fin 2) = 4 := by
  rw [repB_mpv]
  norm_num [Fin.prod_univ_two]
example : ‖mpvState repB 2‖ ^ 2 = 100 := by norm_num [repB_mpvState_norm_sq]

section AxiomChecks
set_option linter.hashCommand false

/-- info: 'MPSTensor.ghzC_eq_ghzSectorTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.ghzC_eq_ghzSectorTensor

/-- info: 'MPSTensor.ghzC_mpv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.ghzC_mpv

/-- info: 'MPSTensor.ghzTensor_mpv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.ghzTensor_mpv

/-- info: 'MPSTensor.ghzB_mpv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.ghzB_mpv

/-- info: 'MPSTensor.ghzB_sameMPV₂Pos_ghzTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.ghzB_sameMPV₂Pos_ghzTensor

/-- info: 'MPSTensor.ghzB_mpvState_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.ghzB_mpvState_eq

/-- info: 'MPSTensor.ghzB_not_sameMPV₂_ghzTensor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.ghzB_not_sameMPV₂_ghzTensor

/-- info: 'MPSTensor.repA_mpv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.repA_mpv

/-- info: 'MPSTensor.repB_mpv_eq_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.repB_mpv_eq_two_mul

/-- info: 'MPSTensor.repB_mpv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.repB_mpv

/-- info: 'MPSTensor.repB_mpvState_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.repB_mpvState_eq

/-- info: 'MPSTensor.ghzB_mpvState_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.ghzB_mpvState_norm_sq

/-- info: 'MPSTensor.repA_mpvState_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.repA_mpvState_norm_sq

/-- info: 'MPSTensor.repB_mpvState_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MPSTensor.repB_mpvState_norm_sq

end AxiomChecks
