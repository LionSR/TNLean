/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.DesignatedMoveCost
import Mathlib.Tactic.FinCases

/-!
# Regression examples for actual finite scanner histories

These examples distinguish the deterministic fill schedule from random charge
choices, including blank and already-assigned slots. They retain repeated
anchor labels, check exact finite path probabilities, and use the actual
fill-then-charge evaluator. Ambient depth is evaluated on an actual lattice
target rather than supplied as a geometric certificate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 83–154 and 331–337, at `openai/math@adc7f124`.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

namespace TNLeanTest.ActualScanHistories

-- Alternation fixes the fill side even when the charge chooses the other side.
example : fillSide 0 = false ∧ fillSide 1 = true ∧ fillSide 2 = false := by
  decide

example :
    ∃ c : ChargeChoices 1 2, (c 0).1 ≠ fillSide 0 ∧ chargeWeight c = (1 / 4 : ℝ) := by
  refine ⟨fun _ ↦ (true, 0), by decide, ?_⟩
  norm_num [chargeWeight]

-- The singleton row is padded to two slots; the second one is genuinely blank.
private theorem singleton_row_slot (t : Fin 2) :
    fillSlot (Finset.univ : Finset (Fin 1)) (fun _ ↦ 1) 2 0 2 false t =
      if t = 0 then some 0 else none := by
  fin_cases t <;>
    simp [fillSlot, initialFront, orientedRow, depthRow, Finset.univ_unique]

example (σ : PhysicalPartition (Fin 1)) :
    fill Finset.univ (fun _ ↦ 1) 2 0 2 2 σ = σ ∧
      fillCount 3 false = fillCount 2 false + 1 := by
  apply fill_blank
  exact singleton_row_slot 1

-- Consuming that blank completes the padded row and advances the nominal front.
example : nominalFront 2 0 2 2 false = 1 ∧ nominalFront 2 0 2 3 false = 2 := by
  norm_num [nominalFront, initialFront, fillCount]

-- A scheduled near fill does not overwrite a site previously assigned to the far side.
example :
    fill Finset.univ (fun _ : Fin 1 ↦ 1) 2 0 2 0 (fun _ ↦ some true) =
        (fun _ ↦ some true) ∧
      fillCount 1 false = fillCount 0 false + 1 := by
  apply fill_assigned _ _ _ _ _ _ _ 0 true
  · exact singleton_row_slot 0
  · rfl

-- Distinct labels at one physical anchor occupy distinct slots, followed by padding.
private theorem repeated_anchor_candidates :
    orderedChargeCandidates (fun _ : Fin 1 ↦ (1 : ℤ)) (fun _ : Fin 2 ↦ 0) 1 1 =
      [0, 1] := by
  simp [orderedChargeCandidates, chargeCandidates, Fin.sort_univ, List.finRange_succ]

example :
    let labels := orderedChargeCandidates (fun _ : Fin 1 ↦ (1 : ℤ))
      (fun _ : Fin 2 ↦ 0) 1 1
    paddedChargeSlot labels 3 0 = some 0 ∧
      paddedChargeSlot labels 3 1 = some 1 ∧ paddedChargeSlot labels 3 2 = none := by
  simp [repeated_anchor_candidates, paddedChargeSlot]

example (i : Fin 2) :
    ∃! slot : Fin 3,
      paddedChargeSlot
        (orderedChargeCandidates (fun _ : Fin 1 ↦ (1 : ℤ)) (fun _ : Fin 2 ↦ 0) 1 1)
        3 slot = some i := by
  apply existsUnique_orderedChargeSlot
  · norm_num [chargeCandidates]
  · norm_num

-- Two offsets and two slots give eight one-band histories after one charge.
example : Fintype.card (History 1 2 2 1) = 8 := by
  norm_num

example (h : History 1 2 2 0) (c : ChargeChoices 1 2) :
    historyWeight h = (1 / 2 : ℝ) ∧
      historyWeight (extendHistory h c) = (1 / 8 : ℝ) := by
  norm_num [historyWeight]

example (h : History 1 2 2 2) : historyWeight h = (1 / 32 : ℝ) := by
  norm_num [historyWeight]

example : (∑ h : History 1 2 2 2, historyWeight h) = 1 :=
  sum_historyWeight 1 2 (by decide) (by decide)

-- Summing over all other bands leaves the selected side-and-slot atom at one quarter.
example :
    (∑ c : ChargeChoices 2 2, if c 0 = (true, 1) then chargeWeight c else 0) =
      (1 / 4 : ℝ) := by
  convert sum_chargeWeight_band (K := 2) (M := 2) (by decide) 0 (true, 1) using 1
  norm_num

example (h : History 1 2 2 0) :
    (∑ c : ChargeChoices 1 2,
      if c 0 = (true, 1) then historyWeight (extendHistory h c) else 0) =
      (1 / 8 : ℝ) := by
  rw [sum_historyWeight_extendHistory_band h (by decide)]
  norm_num [historyWeight]

example :
    (∑ h : History 2 2 2 2, if h.1 0 = 1 then historyWeight h else 0) =
      (1 / 2 : ℝ) :=
  sum_historyWeight_offset (by decide) (by decide) 0 1

-- Both slots on the random far side have total probability one half, at every fill index.
example (k : ℕ) :
    (∑ c : ChargeChoices 1 2, if (c 0).1 ≠ fillSide k then chargeWeight c else 0) =
      (1 / 2 : ℝ) := by
  have hsplit (c : ChargeChoices 1 2) :
      (if (c 0).1 ≠ fillSide k then chargeWeight c else 0) =
        (if c 0 = (!fillSide k, 0) then chargeWeight c else 0) +
          (if c 0 = (!fillSide k, 1) then chargeWeight c else 0) := by
    obtain ⟨side, slot⟩ := c 0
    fin_cases slot <;> cases side <;> cases fillSide k <;> simp
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, sum_chargeWeight_band (by decide),
    sum_chargeWeight_band (by decide)]
  norm_num

-- A genuine evaluated scan: two adjacent active sites and an exterior target site.
private def splitCoordinates (x : Fin 3) : ℤ × ℤ :=
  if x = 0 then (2, 0) else if x = 1 then (3, 0) else (0, 0)

private abbrev splitScan : CollarScan (Fin 3) (Fin 1) where
  graph := {
    Adj := fun x y ↦ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)
    symm := ⟨by tauto⟩
    loopless := ⟨by intro x; simp; omega⟩ }
  A := {0, 1}
  depth := fun x ↦ ambientDepth {(0, 0)} (Finset.singleton_nonempty _) (splitCoordinates x)
  anchor := fun _ ↦ 0
  n := 2
  m := 1
  K := 1
  D := 2
  r₀ := 1
  C₁ := 1

private def splitHistory : History splitScan.K splitScan.m splitScan.M 0 :=
  (fun _ ↦ 0, Fin.elim0)

private theorem split_old_state (x : Fin 3) :
    splitScan.oldChargeState splitHistory 0 x =
      if x = 0 then some false else if x = 1 then none else some true := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  fin_cases x <;>
    norm_num [CollarScan.oldChargeState, CollarScan.state, CollarScan.bandState,
      splitHistory, splitScan, splitCoordinates, ambientDepth, ambientSupDistance,
      CollarScan.lower, CollarScan.upper, fill, fillSide, fillCount, fillSlot,
      initialFront, orientedRow, depthRow, huniv, Finset.filter_insert,
      Finset.filter_singleton, Option.filter, assign, initialPartition]

private theorem split_good : splitScan.IsGoodOldHistory splitHistory := by
  intro g side x hx hs
  have hg : g = 0 := Fin.eq_zero g
  subst g
  rw [split_old_state] at hs
  fin_cases x <;> cases side <;>
    norm_num [splitScan, splitCoordinates, ambientDepth, ambientSupDistance,
      orientedDepth, CollarScan.front, nominalFront, initialFront, fillCount,
      CollarScan.lower, CollarScan.upper, splitHistory] at *

-- The far-side exterior site fails the lead inequality; goodness only quantifies over A.
example :
    splitScan.IsGoodOldHistory splitHistory ∧ (2 : Fin 3) ∉ splitScan.A ∧
      splitScan.oldChargeState splitHistory 0 2 = some true ∧
      ¬ 2 * orientedDepth splitScan.depth true 2 ≤
        2 * splitScan.front 0 0 1 true + splitScan.D := by
  refine ⟨split_good, ?_⟩
  rw [split_old_state]
  norm_num [splitScan, splitCoordinates, ambientDepth, ambientSupDistance,
    orientedDepth, CollarScan.front, nominalFront, initialFront, fillCount,
    CollarScan.lower, CollarScan.upper]

private theorem split_ball_split :
    (splitScan.ball 0 ∩ receiving (splitScan.oldChargeState splitHistory 0) false).Nonempty ∧
      (splitScan.ball 0 ∩ middle (splitScan.oldChargeState splitHistory 0)).Nonempty := by
  have hball0 : (0 : Fin 3) ∈ splitScan.ball 0 := by simp [CollarScan.ball]
  have hball1 : (1 : Fin 3) ∈ splitScan.ball 0 := by
    simp [CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq]
  constructor
  · exact ⟨0, Finset.mem_inter.mpr ⟨hball0, by simp [receiving, split_old_state]⟩⟩
  · exact ⟨1, Finset.mem_inter.mpr ⟨hball1, by simp [middle, split_old_state]⟩⟩

example :
    splitScan.IsGoodOldHistory splitHistory ∧
      (splitScan.ball 0 ∩ receiving (splitScan.oldChargeState splitHistory 0) false).Nonempty ∧
      (splitScan.ball 0 ∩ middle (splitScan.oldChargeState splitHistory 0)).Nonempty :=
  ⟨split_good, split_ball_split⟩

private def splitSlot : Fin splitScan.M :=
  ⟨0, by norm_num [CollarScan.M, chargeSlotCount]⟩

private theorem split_selected : splitScan.selected 0 0 1 (false, splitSlot) = some 0 := by
  norm_num [CollarScan.selected, CollarScan.candidates, paddedChargeSlot,
    orderedChargeCandidates, chargeCandidates, CollarScan.front, nominalFront,
    initialFront, fillCount, CollarScan.lower, CollarScan.upper, orientedDepth,
    splitScan, splitCoordinates, ambientDepth, ambientSupDistance, Finset.univ_unique, splitSlot]

-- The actual extension moves exactly the remaining active site of the split ball.
example (c : ChargeChoices splitScan.K splitScan.M) (hc : c 0 = (false, splitSlot)) :
    middle (splitScan.oldChargeState splitHistory 0) \
        middle (splitScan.state (extendHistory splitHistory c) 0) = {1} := by
  have hsample := splitScan.selected_split_sampling splitHistory 0 false 0 splitSlot
    (by decide) (by decide) (by norm_num) split_selected split_ball_split
  rw [hsample.1 c hc]
  ext x
  fin_cases x <;>
    simp [middle, split_old_state, CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq]

example :
    (∑ c : ChargeChoices splitScan.K splitScan.M,
      if c 0 = (false, splitSlot) then historyWeight (extendHistory splitHistory c) else 0) =
        (1 / 8 : ℝ) := by
  rw [sum_historyWeight_extendHistory_band splitHistory
    (by norm_num [CollarScan.M, chargeSlotCount])]
  norm_num [historyWeight, CollarScan.M, chargeSlotCount]

-- The exterior far site is outside the radius-one ball, so only the near incidence splits.
private theorem split_incidences :
    splitScan.splitIncidences splitHistory 0 = {(false, 0)} := by
  have hfar : splitScan.ball 0 ∩ receiving (splitScan.oldChargeState splitHistory 0) true =
      ∅ := by
    ext x
    fin_cases x <;>
      simp [CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq,
        receiving, split_old_state]
  ext ⟨side, i⟩
  have hi : i = 0 := Fin.eq_zero i
  subst i
  cases side <;> simp [CollarScan.mem_splitIncidences, split_ball_split, hfar]

-- Cardinality is a nonnegative move cost; the incidence sum gives a genuine expectation bound.
example :
    (1 / 8 : ℝ) ≤ ∑ c : ChargeChoices splitScan.K splitScan.M,
      chargeWeight c * splitScan.chargeMoveCost splitHistory (fun _ _ B ↦ (B.card : ℝ)) c := by
  have hslots (g : Fin splitScan.K) (p : Bool × Fin 1)
      (hp : p ∈ splitScan.splitIncidences splitHistory g) :
      ∃ slot : Fin splitScan.M,
        splitScan.selected g (splitHistory.1 g) 1 (p.1, slot) = some p.2 := by
    have hg : g = 0 := Fin.eq_zero g
    subst g
    rw [split_incidences, Finset.mem_singleton] at hp
    subst p
    exact ⟨splitSlot, split_selected⟩
  have hmiddle : splitScan.ball 0 ∩ middle (splitScan.oldChargeState splitHistory 0) = {1} := by
    ext x
    fin_cases x <;>
      simp [middle, split_old_state, CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq]
  have hcost : splitScan.splitIncidenceCost splitHistory (fun _ _ B ↦ (B.card : ℝ)) = 1 := by
    simp [CollarScan.splitIncidenceCost, split_incidences, hmiddle]
  calc
    (1 / 8 : ℝ) = (1 / (2 * (splitScan.M : ℝ))) *
        splitScan.splitIncidenceCost splitHistory (fun _ _ B ↦ (B.card : ℝ)) := by
      rw [hcost]
      norm_num [CollarScan.M, chargeSlotCount]
    _ ≤ _ := splitScan.splitIncidenceCost_le_expected_chargeMoveCost splitHistory
      (fun _ _ B ↦ (B.card : ℝ)) (fun _ _ B ↦ Nat.cast_nonneg B.card) hslots

-- The actual compact truncation set contains the anchor, so the genuine
-- variable-radius designated support is the charge ball in this split history.
example : TNLean.PEPS.AreaLaw.designatedSupport splitScan.graph
    (splitScan.truncationSet 8) splitScan.r₀ (splitScan.anchor 0) = splitScan.ball 0 := by
  have hm : splitScan.anchor 0 ∈ splitScan.truncationSet 8 := by
    norm_num [CollarScan.truncationSet, splitScan, splitCoordinates,
      ambientDepth, ambientSupDistance]
  have hd : TNLean.PEPS.AreaLaw.setDist splitScan.graph (splitScan.truncationSet 8)
      (splitScan.anchor 0) = 0 := by
    apply le_antisymm _ zero_le
    have hb : TNLean.PEPS.AreaLaw.setDist splitScan.graph (splitScan.truncationSet 8)
        (splitScan.anchor 0) ≤ splitScan.graph.edist (splitScan.anchor 0) (splitScan.anchor 0) :=
      Finset.inf_le hm
    simpa only [SimpleGraph.edist_self] using hb
  simp [TNLean.PEPS.AreaLaw.designatedSupport, hd, TNLean.PEPS.AreaLaw.truncationRadius,
    QuantumCircuit.graphBall, CollarScan.ball]

section ActualEvaluator

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) {k : ℕ} (h : History S.K S.m S.M k)
  (c : ChargeChoices S.K S.M) (g : Fin S.K)

-- The appended charge reads the partition and nominal index after its preceding fill.
example :
    S.state (extendHistory h c) g =
      S.chargeStep g (h.1 g) (k + 1) (c g)
        (fill S.A S.depth S.n (S.lower g (h.1 g)) (S.upper g (h.1 g)) k
          (S.state h g)) :=
  S.state_extendHistory h c g

-- Appending random choices cannot move either post-fill nominal front.
example (side : Bool) :
    S.front g ((extendHistory h c).1 g) (k + 1) side =
      S.front g (h.1 g) (k + 1) side :=
  S.front_extendHistory h g c side

end ActualEvaluator

-- Ambient depth sees sup-norm distance from the target, including diagonal sites.
example : ambientDepth {(0, 0)} (Finset.singleton_nonempty _) (3, -4) = 4 := by
  norm_num [ambientDepth, ambientSupDistance]

example :
    (depthRow (fun x : Fin 2 ↦ ambientDepth {(0, 0)} (Finset.singleton_nonempty _)
      (if x = 0 then (1, 0) else (3, -4))) 1).length = 1 := by
  classical
  norm_num [depthRow, ambientDepth, ambientSupDistance, Finset.univ_fin2,
    Finset.filter_insert, Finset.filter_singleton]

end TNLeanTest.ActualScanHistories

section AxiomChecks

set_option linter.hashCommand false

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.state_extendHistory'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.state_extendHistory

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.oldChargeState_front_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.oldChargeState_front_le

/--
info: 'TNLean.PEPS.AreaLaw.Scan.sum_historyWeight'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_historyWeight

/--
info: 'TNLean.PEPS.AreaLaw.Scan.sum_historyWeight_extendHistory_band'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sum_historyWeight_extendHistory_band

/--
info: 'TNLean.PEPS.AreaLaw.Scan.existsUnique_orderedChargeSlot'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms existsUnique_orderedChargeSlot

/--
info: 'TNLean.PEPS.AreaLaw.Scan.abs_ambientDepth_sub_le_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms abs_ambientDepth_sub_le_domainGraph

/--
info: 'TNLean.PEPS.AreaLaw.Scan.depthRow_ambientDepth_length_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms depthRow_ambientDepth_length_le

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.selected_split_sampling'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.selected_split_sampling

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.good_split_sampling_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.good_split_sampling_domainGraph

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.splitIncidenceCost_le_expected_chargeMoveCost'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.splitIncidenceCost_le_expected_chargeMoveCost

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.good_splitIncidenceCost_le_expected_chargeMoveCost_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.good_splitIncidenceCost_le_expected_chargeMoveCost_domainGraph

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.middle_subset_truncationSet'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.middle_subset_truncationSet

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.designatedSupport_eq_ball_of_split'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.designatedSupport_eq_ball_of_split

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.good_designated_split_sampling_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.good_designated_split_sampling_domainGraph

/--
info: 'TNLean.PEPS.AreaLaw.Scan.CollarScan.good_designatedSplitIncidenceCost_le_expected_chargeMoveCost_domainGraph'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CollarScan.good_designatedSplitIncidenceCost_le_expected_chargeMoveCost_domainGraph

end AxiomChecks
