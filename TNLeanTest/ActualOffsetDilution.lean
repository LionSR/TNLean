/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.OffsetDilution

/-!
# Actual-front interval dilution regressions

Both oriented fronts attain the asymmetric interval bound at four distinct
offsets. A physical event in the evaluated initial partition has those same
four offsets and attains probability one half. These checks use the exact
history marginal, without enumerating the charge-history product space.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–154, at `openai/math@adc7f124`.
-/

set_option autoImplicit false
set_option linter.hashCommand false


open TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

namespace TNLeanTest.ActualOffsetDilution

private abbrev scan : CollarScan (Fin 2) (Fin 1) where
  graph := ⊥
  A := Finset.univ
  depth := fun x ↦ if x = 0 then 9 else 13
  anchor := fun _ ↦ 0
  n := 2
  m := 8
  K := 1
  D := 1
  r₀ := 0
  C₁ := 1

-- Each orientation contains four offsets, attaining a + b + 1 for a = 1, b = 2.
example :
    (Finset.univ.filter fun r : Fin scan.m ↦
      scan.front 0 r 0 false - 1 ≤ 12 ∧ 12 ≤ scan.front 0 r 0 false + 2).card = 4 := by
  decide

example :
    (Finset.univ.filter fun r : Fin scan.m ↦
      scan.front 0 r 0 true - 1 ≤ -43 ∧ -43 ≤ scan.front 0 r 0 true + 2).card = 4 := by
  decide

-- Reducing the interval-length bound by one is genuinely false.
example : ¬((Finset.univ.filter fun r : Fin scan.m ↦
    scan.front 0 r 0 false - 1 ≤ 12 ∧ 12 ≤ scan.front 0 r 0 false + 2).card ≤ 3) := by
  decide

-- The same exact offset marginal holds after arbitrarily many charge rounds.
example (k : ℕ) :
    (∑ h : History 2 8 2 k,
      if h.1 0 ∈ ({1, 2, 3, 4} : Finset (Fin 8)) then historyWeight h else 0) =
      (1 / 2 : ℝ) := by
  rw [sum_historyWeight_offset_mem (by decide) (by decide)]
  norm_num

-- The old-history/charge double sum is the same completed-history marginal.
example (k : ℕ) :
    (∑ h : History 2 8 2 k, ∑ c : ChargeChoices 2 2,
      historyWeight h * chargeWeight c *
        (if (extendHistory h c).1 0 ∈ ({1, 2, 3, 4} : Finset (Fin 8))
          then 1 else 0)) = (1 / 2 : ℝ) := by
  rw [← sum_historyWeight_mul_eq_sum_extendHistory
    (fun h : History 2 8 2 (k + 1) ↦
      if h.1 0 ∈ ({1, 2, 3, 4} : Finset (Fin 8)) then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_historyWeight_offset_mem (by decide) (by decide)]
  norm_num

private def evaluatedEvent (h : History scan.K scan.m scan.M 0) : Prop :=
  scan.state h 0 0 = some false ∧ scan.state h 0 1 = none

private theorem evaluatedEvent_iff (h : History scan.K scan.m scan.M 0) :
    evaluatedEvent h ↔ h.1 0 ∈ ({1, 2, 3, 4} : Finset (Fin 8)) := by
  simp [evaluatedEvent, CollarScan.state, CollarScan.bandState, initialPartition,
    CollarScan.lower, CollarScan.upper, scan]
  simp only [Fin.ext_iff]
  split_ifs <;> simp_all <;> omega

-- This event reads the actual partition: the first site is near, the second is middle.
open Classical in
example :
    (∑ h : History scan.K scan.m scan.M 0,
      if evaluatedEvent h then historyWeight h else 0) = (1 / 2 : ℝ) := by
  classical
  simp_rw [evaluatedEvent_iff]
  rw [sum_historyWeight_offset_mem (K := scan.K) (m := scan.m)
    (M := scan.M) (k := 0) (by decide)
    (chargeSlotCount_pos (by norm_num) (by decide) (by decide))]
  norm_num

open Classical in
example :
    (∑ h : History scan.K scan.m scan.M 0,
      if evaluatedEvent h then historyWeight h else 0) ≤ (1 / 2 : ℝ) := by
  classical
  have h := scan.sum_historyWeight_event_le (by decide)
    (chargeSlotCount_pos (by norm_num) (by decide) (by decide)) 0 0 false 12 1 2
    evaluatedEvent (fun h he ↦ ?_)
  · norm_num [scan] at h ⊢
    exact h
  · rw [evaluatedEvent_iff] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with he | he | he | he <;>
      simp [he, CollarScan.front, nominalFront, initialFront, fillCount, CollarScan.lower, scan]

/--
info: 'TNLean.PEPS.AreaLaw.Scan.sum_historyWeight_mul_eq_sum_extendHistory' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.sum_historyWeight_mul_eq_sum_extendHistory

/-- info: 'TNLean.PEPS.AreaLaw.Scan.sum_historyWeight_offset_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.sum_historyWeight_offset_mem

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.front_injective_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.front_injective_offset

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.card_front_interval_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.card_front_interval_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_event_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_exists_band_side_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.sum_historyWeight_exists_band_side_le

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.historyWeight_mixture_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.Scan.CollarScan.historyWeight_mixture_event_le

end TNLeanTest.ActualOffsetDilution
