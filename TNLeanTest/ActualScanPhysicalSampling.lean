/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ExpectedMoveCost
import TNLean.PEPS.AreaLaw.Scan.DesignatedDilution

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

private def domain : Finset (ℤ × ℤ) :=
  {(0, 0), (33, 0), (34, 0), (1000, 0), (1001, 0), (5000, 0)}

private def target : Finset (ℤ × ℤ) := {(0, 0), (5000, 0)}

private theorem target_nonempty : target.Nonempty := by simp [target]

private def p0 : Site domain := ⟨(0, 0), by simp [domain]⟩
private def p33 : Site domain := ⟨(33, 0), by simp [domain]⟩
private def p34 : Site domain := ⟨(34, 0), by simp [domain]⟩
private def p1000 : Site domain := ⟨(1000, 0), by simp [domain]⟩
private def p1001 : Site domain := ⟨(1001, 0), by simp [domain]⟩
private def p5000 : Site domain := ⟨(5000, 0), by simp [domain]⟩

private theorem site_eq_iff (x y : Site domain) : x = y ↔ x.val = y.val :=
  ⟨congrArg Subtype.val, Subtype.ext⟩

private theorem site_cases (x : Site domain) :
    x = p0 ∨ x = p33 ∨ x = p34 ∨ x = p1000 ∨ x = p1001 ∨ x = p5000 := by
  have hx := x.property
  simp only [domain, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h)))))

private abbrev scan : CollarScan (Site domain) (Fin 1) where
  graph := domainGraph domain
  A := Finset.univ.filter fun x ↦ x.val.1 ≤ 1000
  depth := fun x ↦ ambientDepth target target_nonempty x.val
  anchor := fun _ ↦ p33
  n := 600000
  m := 32
  K := 1
  D := 2
  r₀ := 1
  C₁ := 3

private def history : History scan.K scan.m scan.M 0 :=
  (fun _ ↦ 0, Fin.elim0)

private theorem row_thirtyThree : depthRow scan.depth 33 = [p33] := by
  have hf : (Finset.univ.filter fun x ↦ scan.depth x = 33) = {p33} := by
    ext x
    rcases site_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [scan, target, ambientDepth, ambientSupDistance,
        p0, p33, p34, p1000, p1001, p5000, site_eq_iff]
  simp only [depthRow, hf, Finset.toList_singleton]

private theorem first_fill_slot :
    fillSlot scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0) false 0 =
      some p33 := by
  change fillSlot scan.A scan.depth 600000 32 160 false 0 = some p33
  change ((depthRow scan.depth 33)[0]?).filter (fun x ↦ x ∈ scan.A) = some p33
  rw [row_thirtyThree]
  norm_num [scan, p33]

private theorem old_state (x : Site domain) :
    scan.oldChargeState history 0 x =
      if x = p0 ∨ x = p33 then some false else if x = p34 then none else some true := by
  have hs : fillSlot scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0)
      (fillSide 0) (fillCount 0 (fillSide 0)) = some p33 := by
    simpa [fillSide, fillCount] using first_fill_slot
  simp only [CollarScan.oldChargeState, history, Fin.val_zero,
    CollarScan.state, CollarScan.bandState, fill, hs]
  rcases site_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [assign, initialPartition, scan, target, ambientDepth, ambientSupDistance,
      CollarScan.lower, CollarScan.upper, fillSide, p0, p33, p34, p1000, p1001, p5000, site_eq_iff]

private theorem good_history : scan.IsGoodOldHistory history := by
  intro g side x hx hs
  have hg : g = 0 := Fin.eq_zero g
  subst g
  rw [old_state] at hs
  rcases site_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;> cases side <;>
    norm_num [scan, p0, p33, p34, p1000, p1001, p5000, site_eq_iff, target, ambientDepth,
      ambientSupDistance, orientedDepth, CollarScan.front, nominalFront,
      initialFront, fillCount, CollarScan.lower, CollarScan.upper, history] at *

private theorem ball_split :
    (scan.ball 0 ∩ receiving (scan.oldChargeState history 0) false).Nonempty ∧
      (scan.ball 0 ∩ middle (scan.oldChargeState history 0)).Nonempty := by
  have hb9 : p33 ∈ scan.ball 0 := by simp [CollarScan.ball]
  have hb10 : p34 ∈ scan.ball 0 := by
    simp [CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq,
      domainGraph, p33, p34]
  constructor
  · exact ⟨p33, Finset.mem_inter.mpr ⟨hb9, by simp [receiving, old_state]⟩⟩
  · exact ⟨p34, Finset.mem_inter.mpr ⟨hb10, by
      norm_num [middle, old_state, p0, p33, p34, site_eq_iff]⟩⟩

private theorem ambient_rows (d : ℕ) (_hd : 1 ≤ d) (hdL : d ≤ 256) :
    (ambientDilation target d \ ambientDilation target (d - 1)).card ≤ scan.n := by
  calc
    _ ≤ (ambientDilation target d).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ (2 * d + 1) ^ 2 * target.card := Geometry.card_ambientDilation_le target d
    _ ≤ (2 * 256 + 1) ^ 2 * 2 := by
      have ht : target.card = 2 := by norm_num [target]
      rw [ht]
      exact Nat.mul_le_mul_right 2 (Nat.pow_le_pow_left (by omega) 2)
    _ ≤ scan.n := by norm_num

private theorem boundary_endpoints :
    Geometry.boundaryEndpoints domain scan.A = {(1000, 0), (1001, 0)} := by
  classical
  have hcut : edgeBoundary domain scan.A = {s(p1000, p1001)} := by
    ext e
    constructor
    · intro he
      obtain ⟨he, x, hx, y, hy, rfl⟩ := Finset.mem_filter.mp he
      have hadj : (domainGraph domain).Adj x y := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      rcases site_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases site_cases y with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [scan, domainGraph, p0, p33, p34, p1000, p1001, p5000, site_eq_iff] at *
    · intro he
      have heq : e = s(p1000, p1001) := Finset.mem_singleton.mp he
      subst e
      refine Finset.mem_filter.mpr ⟨?_, p1000, ?_, p1001, ?_, rfl⟩
      · apply SimpleGraph.mem_edgeFinset.mpr
        change (domainGraph domain).Adj p1000 p1001
        norm_num [domainGraph, p1000, p1001]
      · norm_num [scan, p1000]
      · norm_num [scan, p1001]
  rw [Geometry.boundaryEndpoints, hcut]
  simp [Sym2.toFinset_mk_eq, p1000, p1001]

private theorem clearance : ∀ t ∈ target,
    ∀ z ∈ Geometry.boundaryEndpoints domain scan.A,
      ((2 * 256 + 10 * scan.r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
  rw [boundary_endpoints]
  simp only [target, Finset.mem_insert, Finset.mem_singleton]
  rintro t (rfl | rfl) z (rfl | rfl) <;> norm_num [scan, ambientSupDistance]

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
private theorem designated_ball :
    designatedSupport scan.graph (scan.truncationSet 256) scan.r₀ (scan.anchor 0) =
      scan.ball 0 := by
  have ha : scan.anchor 0 ∈ scan.truncationSet 256 := by
    norm_num [CollarScan.truncationSet, scan, p33, ambientDepth, target, ambientSupDistance]
  have hd : setDist scan.graph (scan.truncationSet 256) (scan.anchor 0) = 0 := by
    apply le_antisymm _ zero_le
    exact (Finset.inf_le ha).trans (by simp)
  simp [designatedSupport, hd, truncationRadius, QuantumCircuit.graphBall, CollarScan.ball]

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
