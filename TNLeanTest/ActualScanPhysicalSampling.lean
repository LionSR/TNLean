/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLeanTest.ActualScanPhysicalSamplingData

/-!
# A nonempty physical good-history sampling regression

A sparse induced lattice domain contains an adjacent pair at depths 33 and
34 and a genuine cut edge at coordinates 1000 and 1001. The two target sites
lie on opposite sides of the cut. The full numerical margins, ambient layer
bound, cut clearance, good old history, and splitting radius-one ball hold
simultaneously. The sampling conclusion uses the actual domain-graph theorem.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 43–59 and 331–337, at `openai/math@adc7f124`.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

namespace TNLeanTest.ActualScanPhysicalSampling

noncomputable section

-- The geometry is genuinely nonempty, with both target colors and a real cut edge.
example : p0 ∈ scan.A ∧ p5000 ∉ scan.A ∧
    p0.val ∈ target ∧ p5000.val ∈ target ∧
    (Geometry.boundaryEndpoints domain scan.A).Nonempty := by
  rw [boundary_endpoints]
  norm_num [scan, p0, p5000, target]

-- All physical and numerical hypotheses are discharged on this single scan.
example : ∃! slot : Fin scan.M,
    scan.selected 0 0 1 (false, slot) = some 0 ∧
    (∀ c : ChargeChoices scan.K scan.M, c 0 = (false, slot) →
      middle (scan.oldChargeState history 0) \ middle (scan.state (extendHistory history c) 0) =
        scan.ball 0 ∩ middle (scan.oldChargeState history 0)) ∧
    (∑ c : ChargeChoices scan.K scan.M, if c 0 = (false, slot) then chargeWeight c else 0) =
      1 / (2 * (scan.M : ℝ)) ∧
    0 < 1 / (2 * (scan.C₁ + 1)) ∧
    (1 / (2 * (scan.C₁ + 1))) / ((scan.n : ℝ) * scan.D) ≤
      ∑ c : ChargeChoices scan.K scan.M, if c 0 = (false, slot) then chargeWeight c else 0 := by
  apply CollarScan.good_split_sampling_domainGraph target_nonempty scan rfl rfl
    history 0 false 0 (L := 256) (μ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows
  · intro x
    exact (Finset.card_filter_le _ _).trans (by simp)
  · exact clearance
  · exact good_history
  · exact ball_split


-- Cardinality cost gives a strictly positive expectation on the same physical scan.
example : (1 / 9600000 : ℝ) ≤
    ∑ c : ChargeChoices scan.K scan.M,
      chargeWeight c * scan.chargeMoveCost history (fun _ _ B ↦ (B.card : ℝ)) c := by
  classical
  have hcost : 1 ≤ scan.splitIncidenceCost history (fun _ _ B ↦ (B.card : ℝ)) := by
    simp only [CollarScan.splitIncidenceCost, Finset.univ_unique, Finset.sum_singleton]
    have hmem : (false, (0 : Fin 1)) ∈ scan.splitIncidences history 0 :=
      (scan.mem_splitIncidences history 0 (false, 0)).mpr ball_split
    calc
      (1 : ℝ) ≤ (scan.ball 0 ∩ middle (scan.oldChargeState history 0)).card := by
        exact_mod_cast Finset.one_le_card.mpr ball_split.2
      _ ≤ _ := Finset.single_le_sum
        (f := fun p : Bool × Fin 1 ↦
          ((scan.ball p.2 ∩ middle (scan.oldChargeState history 0)).card : ℝ))
        (fun p _ ↦ Nat.cast_nonneg
          (scan.ball p.2 ∩ middle (scan.oldChargeState history 0)).card) hmem
  have hmult (x : Site domain) :
      (Finset.univ.filter fun i ↦ scan.anchor i = x).card ≤ 1 :=
    (Finset.card_filter_le _ _).trans (by simp)
  have hbound := CollarScan.good_splitIncidenceCost_le_expected_chargeMoveCost_domainGraph
    target_nonempty scan rfl rfl history (fun _ _ B ↦ (B.card : ℝ))
    (fun _ _ B ↦ Nat.cast_nonneg B.card) (L := 256) (μ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows hmult clearance good_history
  calc
    (1 / 9600000 : ℝ) =
        ((1 / (2 * (scan.C₁ + 1))) / ((scan.n : ℝ) * scan.D)) * 1 := by norm_num
    _ ≤ ((1 / (2 * (scan.C₁ + 1))) / ((scan.n : ℝ) * scan.D)) *
        scan.splitIncidenceCost history (fun _ _ B ↦ (B.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hcost (by norm_num)
    _ ≤ _ := hbound.2

-- The designated support really splits on this physical history.

example : scan.designatedSplitIncidence (scan.oldChargeState history 0) 256 0 false := by
  unfold CollarScan.designatedSplitIncidence
  rw [designated_ball]
  exact ball_split

-- This fixed-side event has a nontrivial probability bound, with no goodness input.
open Classical in
example : (∑ h : History scan.K scan.m scan.M 0,
    if scan.designatedSplitIncidence (scan.oldChargeState h 0) 256 0 false
    then historyWeight h else 0) ≤ (3 / 16 : ℝ) := by
  classical
  have hb := scan.sum_historyWeight_event_le (k := 0) (by norm_num)
    (chargeSlotCount_pos (by norm_num) (by norm_num) (by norm_num))
    0 1 false (orientedDepth scan.depth false (scan.anchor 0)) 1 4
    (fun h ↦ scan.designatedSplitIncidence (scan.oldChargeState h 0) 256 0 false)
    (fun h hs ↦ ?_)
  · norm_num at hb ⊢
    exact hb
  · have heq := scan.designatedSupport_eq_ball_of_split h 0 false 0 (by norm_num) hs
    have hsplit : (scan.ball 0 ∩ receiving (scan.oldChargeState h 0) false).Nonempty ∧
        (scan.ball 0 ∩ middle (scan.oldChargeState h 0)).Nonempty := by
      simpa only [CollarScan.designatedSplitIncidence, heq] using hs
    have hi := CollarScan.old_split_anchor_bounds_domainGraph target_nonempty scan rfl rfl
      h 0 false 0 (by norm_num) (by norm_num) ambient_rows clearance hsplit
    norm_num only [scan, Nat.cast_ofNat, Int.reduceAdd, Int.reduceMul, add_assoc] at hi ⊢
    exact hi

-- Both old/new common-p distributions instantiate on the same nonempty geometry.
open Classical in
example {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * (∑ h : History scan.K scan.m scan.M 0,
      if ∃ g side, scan.designatedSplitIncidence (scan.oldChargeState h g) 256 0 side
      then historyWeight h else 0) +
    p * (∑ h : History scan.K scan.m scan.M 1,
      if ∃ g side, scan.designatedSplitIncidence (scan.state h g) 256 0 side
      then historyWeight h else 0) ≤ (5 / 8 : ℝ) := by
  have h := CollarScan.designated_split_mixture_dilution_domainGraph target_nonempty scan rfl rfl
    (k := 0) (L := 256) 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows clearance hp0 hp1
  norm_num at h ⊢
  exact h


end

end TNLeanTest.ActualScanPhysicalSampling
