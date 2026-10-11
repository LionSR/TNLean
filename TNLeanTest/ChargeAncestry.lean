/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalChargeAncestry
import TNLean.PEPS.AreaLaw.Scan.AncestryGeometry
import Mathlib.Tactic.FinCases

/-!
# Regressions for actual charge ancestry

A real evaluated charge moves a middle site ahead of its nominal front. The
ancestry theorem extracts a nonempty path, rather than accepting that path as
an input. Separate arithmetic checks pin the pair-time clock and its rounding.
-/

set_option autoImplicit false
set_option linter.hashCommand false

open TNLean.PEPS.AreaLaw.Scan

namespace TNLeanTest.ChargeAncestry

private abbrev scan : CollarScan (Fin 3) (Fin 1) where
  graph := ⊤
  A := Finset.univ
  depth := fun x ↦ (x.val : ℤ) + 1
  anchor := fun _ ↦ 1
  n := 10
  m := 1
  K := 1
  D := 1
  r₀ := 1
  C₁ := 1

private def slot : Fin scan.M := ⟨0, by norm_num [CollarScan.M, chargeSlotCount]⟩
private def choices (_ : ℕ) : Bool × Fin scan.M := (false, slot)

private theorem ball_eq : scan.ball 0 = Finset.univ := by
  ext x
  simp only [CollarScan.ball, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.edist_top]
  split_ifs <;> norm_num [scan]

private theorem selected_eq : scan.selected 0 0 1 (choices 0) = some 0 := by
  norm_num [CollarScan.selected, CollarScan.candidates, paddedChargeSlot,
    orderedChargeCandidates, chargeCandidates, CollarScan.front, nominalFront,
    initialFront, fillCount, CollarScan.lower, CollarScan.upper, orientedDepth,
    scan, choices, slot, Finset.univ_unique]

private noncomputable def oldState : PhysicalPartition (Fin 3) :=
  fill scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0) 0
    (scan.bandState 0 0 0 (fun j ↦ choices j))

private theorem old_state (x : Fin 3) : oldState x =
    if x = 2 then none else some false := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  fin_cases x <;>
    norm_num [oldState, CollarScan.bandState, scan, CollarScan.lower, CollarScan.upper,
      fill, fillSide, fillCount, fillSlot, initialFront, orientedRow, depthRow,
      huniv, Finset.filter_insert, Finset.filter_singleton, Option.filter,
      assign, initialPartition]

private theorem assigned : scan.bandState 0 0 1 (fun j ↦ choices j) 2 = some false := by
  have hs : (scan.ball 0 ∩ receiving oldState false).Nonempty ∧
      (scan.ball 0 ∩ middle oldState).Nonempty := by
    constructor
    · exact ⟨0, by simp [ball_eq, receiving, old_state]⟩
    · exact ⟨2, by simp [ball_eq, middle, old_state]⟩
  change scan.chargeStep 0 0 1 (choices 0) oldState 2 = some false
  simp only [CollarScan.chargeStep, selected_eq]
  change charge oldState false (scan.ball 0) 2 = some false
  rw [charge, ite_eq_left hs]
  simp [assign, ball_eq, old_state]

private theorem bad : 2 * scan.front 0 0 1 false + scan.D <
    2 * orientedDepth scan.depth false 2 := by
  norm_num [CollarScan.front, nominalFront, initialFront, fillCount,
    CollarScan.lower, CollarScan.upper, orientedDepth, scan]

-- The actual evaluator supplies the path; no ancestry witness is a hypothesis.
example : ∃ events, scan.ChargeAncestry 0 0 choices false 1 2 events ∧
    events ≠ [] ∧ (scan.D : ℤ) < 4 * scan.r₀ * events.length := by
  obtain ⟨events, he⟩ := scan.bandState_has_chargeAncestry 0 0 choices
    (fun _ _ _ _ ↦ Finset.subset_univ _) 1 false 2 (Finset.mem_univ _) assigned
  have hv : ∀ i x, x ∈ scan.ball i →
      |scan.depth x - scan.depth (scan.anchor i)| ≤ scan.r₀ := by
    intro i x _
    fin_cases x <;> norm_num [scan]
  have hb := he.bad_length_and_time scan (by decide) hv bad
  exact ⟨events, he, hb.1, hb.2.1⟩

-- Twenty consumed pairs complete one row on each side when n=10.
example : scan.front 0 0 20 false - scan.front 0 0 0 false = 1 ∧
    scan.front 0 0 20 true - scan.front 0 0 0 true = 1 := by
  norm_num [CollarScan.front, nominalFront, initialFront, fillCount, scan]

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.bandState_has_chargeAncestry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.bandState_has_chargeAncestry

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.ChargeAncestry.bad_length_and_time'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.ChargeAncestry.bad_length_and_time

/-- info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.bad_bandState_has_long_chargeAncestry_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.bad_bandState_has_long_chargeAncestry_domainGraph

end TNLeanTest.ChargeAncestry
