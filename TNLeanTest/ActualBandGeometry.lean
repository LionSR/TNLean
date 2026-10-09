/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TerminalSplits
import TNLean.PEPS.AreaLaw.Scan.SplitCounting

/-!
# Two active physical bands with a genuine cut

The first radius-one support joins depths 12, 13, and 14, and the second joins
108, 109, and 110. Both split before and after the first scheduled fill. A real
cut edge at 1000--1001 is separated from the nonempty target. All hypotheses
of the actual terminal-split and labelled-count theorems hold simultaneously.
Two distinct interaction labels deliberately share the first anchor.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

namespace TNLeanTest.ActualBandGeometry
noncomputable section

private def domain : Finset (ℤ × ℤ) := {(0, 0), (12, 0), (13, 0), (14, 0), (108, 0), (109, 0),
    (110, 0), (1000, 0), (1001, 0)}
private def target : Finset (ℤ × ℤ) := {(0, 0)}
private theorem target_nonempty : target.Nonempty := by simp [target]
private def p0 : Site domain := ⟨(0, 0), by simp [domain]⟩
private def p12 : Site domain := ⟨(12, 0), by simp [domain]⟩
private def p13 : Site domain := ⟨(13, 0), by simp [domain]⟩
private def p14 : Site domain := ⟨(14, 0), by simp [domain]⟩
private def p108 : Site domain := ⟨(108, 0), by simp [domain]⟩
private def p109 : Site domain := ⟨(109, 0), by simp [domain]⟩
private def p110 : Site domain := ⟨(110, 0), by simp [domain]⟩
private def p1000 : Site domain := ⟨(1000, 0), by simp [domain]⟩
private def p1001 : Site domain := ⟨(1001, 0), by simp [domain]⟩
private theorem site_eq_iff (x y : Site domain) : x = y ↔ x.val = y.val :=
  ⟨congrArg Subtype.val, Subtype.ext⟩

private theorem site_cases (x : Site domain) :
    x = p0 ∨ x = p12 ∨ x = p13 ∨ x = p14 ∨ x = p108 ∨ x = p109 ∨ x = p110 ∨ x = p1000
     ∨ x = p1001 := by
  have hx := x.property
  simp only [domain, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h | h | h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h))))))))

private abbrev scan : CollarScan (Site domain) (Fin 3) where
  graph := domainGraph domain
  A := Finset.univ.erase p1001
  depth := fun x ↦ ambientDepth target target_nonempty x.val
  anchor := fun i ↦ if i.val < 2 then p13 else p109
  n := 200000
  m := 12
  K := 2
  D := 1
  r₀ := 1
  C₁ := 9

private def history : History scan.K scan.m scan.M 0 := (fun _ ↦ 0, Fin.elim0)

private theorem ambient_rows (d : ℕ) (_hd : 1 ≤ d) (hdL : d ≤ 192) :
    (ambientDilation target d \ ambientDilation target (d - 1)).card ≤ scan.n := by
  calc
    _ ≤ (ambientDilation target d).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ (2 * d + 1) ^ 2 * target.card := Geometry.card_ambientDilation_le target d
    _ ≤ (2 * 192 + 1) ^ 2 * 1 := by
      rw [show target.card = 1 by simp [target]]
      exact Nat.mul_le_mul_right 1 (Nat.pow_le_pow_left (by omega) 2)
    _ ≤ scan.n := by norm_num

private theorem boundary_endpoints :
    Geometry.boundaryEndpoints domain scan.A = {(1000, 0), (1001, 0)} := by
  classical
  have hcut : edgeBoundary domain scan.A = {s(p1000, p1001)} := by
    ext e
    constructor
    · intro he
      obtain ⟨he, x, hx, y, hy, rfl⟩ := Finset.mem_filter.mp he
      have hy' : y = p1001 := by simpa [scan] using hy
      subst y
      have hadj : (domainGraph domain).Adj x p1001 := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      rcases site_cases x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [scan, domainGraph, p0, p12, p13, p14, p108, p109, p110, p1000, p1001,
    site_eq_iff] at *
    · intro he
      have heq : e = s(p1000, p1001) := Finset.mem_singleton.mp he
      subst e
      refine Finset.mem_filter.mpr ⟨?_, p1000, ?_, p1001, ?_, rfl⟩
      · apply SimpleGraph.mem_edgeFinset.mpr
        change (domainGraph domain).Adj p1000 p1001
        norm_num [domainGraph, p1000, p1001]
      · norm_num [scan, p1000, p1001, site_eq_iff]
      · simp
  rw [Geometry.boundaryEndpoints, hcut]
  simp [Sym2.toFinset_mk_eq, p1000, p1001]

private theorem clearance : ∀ t ∈ target,
    ∀ z ∈ Geometry.boundaryEndpoints domain scan.A,
      ((2 * 192 + 10 * scan.r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
  rw [boundary_endpoints]
  simp only [target, Finset.mem_insert, Finset.mem_singleton]
  rintro t rfl z (rfl | rfl) <;> norm_num [scan, ambientSupDistance]

private theorem designated_eq_ball (i : Fin 3) :
    designatedSupport scan.graph (scan.truncationSet 192) scan.r₀ (scan.anchor i) =
      scan.ball i := by
  have ha : scan.anchor i ∈ scan.truncationSet 192 := by
    fin_cases i <;>
      norm_num [CollarScan.truncationSet, scan, target, ambientDepth,
        ambientSupDistance, p13, p109, p1001, site_eq_iff]
  have hz : setDist scan.graph (scan.truncationSet 192) (scan.anchor i) = 0 := by
    apply le_antisymm _ bot_le
    exact (Finset.inf_le ha).trans (by simp)
  rw [designatedSupport, hz]
  simp [truncationRadius, CollarScan.ball, QuantumCircuit.graphBall]

private theorem initial_split (g : Fin 2) :
    scan.designatedSplitIncidence (scan.state history g) 192 (if g = 0 then 0 else 2) false := by
  rw [CollarScan.designatedSplitIncidence, designated_eq_ball]
  fin_cases g
  · constructor
    · refine ⟨p12, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq,
          domainGraph, p13, p12]
      · norm_num [receiving, CollarScan.state, CollarScan.bandState, history,
          initialPartition, CollarScan.lower, CollarScan.upper, scan, target,
          ambientDepth, ambientSupDistance, p12, p1001, site_eq_iff]
    · refine ⟨p13, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [CollarScan.ball]
      · norm_num [middle, CollarScan.state, CollarScan.bandState, history,
          initialPartition, CollarScan.lower, CollarScan.upper, scan, target,
          ambientDepth, ambientSupDistance, p13, p1001, site_eq_iff]
  · constructor
    · refine ⟨p108, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq,
          domainGraph, p109, p108]
      · norm_num [receiving, CollarScan.state, CollarScan.bandState, history,
          initialPartition, CollarScan.lower, CollarScan.upper, scan, target,
          ambientDepth, ambientSupDistance, p108, p1001, site_eq_iff]
    · refine ⟨p109, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [CollarScan.ball]
      · norm_num [middle, CollarScan.state, CollarScan.bandState, history,
          initialPartition, CollarScan.lower, CollarScan.upper, scan, target,
          ambientDepth, ambientSupDistance, p109, p1001, site_eq_iff]

-- Each of the two genuinely splitting supports meets exactly one receiving
-- side and lies in a single physical part of the other band.
example (g : Fin 2) : IsTerminalSplit (scan.state history)
    (designatedSupport scan.graph (scan.truncationSet 192) scan.r₀
      (scan.anchor (if g = 0 then 0 else 2))) g false := by
  exact CollarScan.state_designatedSplitIncidence_isTerminalSplit_domainGraph
    target_nonempty scan rfl rfl history (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows clearance
    g false _ (initial_split g)

-- This is an actual two-band inclusion, and the theorem also permits independent
-- later histories and times.
example {k : ℕ} (h : History scan.K scan.m scan.M k) :
    receiving (scan.state history 0) false ∪ middle (scan.state history 0) ⊆
      receiving (scan.state h 1) false :=
  scan.state_near_middle_subset_later_near history h 0 1 (by decide)

-- Repeated anchors remain separate labels in the physical count.
example : (0 : Fin 3) ≠ 1 ∧ scan.anchor 0 = scan.anchor 1 := by norm_num [scan]

open Classical in
example : (∑ g : Fin scan.K, ∑ side : Bool,
    (Finset.univ.filter fun i ↦
      scan.designatedSplitIncidence (scan.state history g) 192 i side).card) ≤
    10 * scan.K * scan.n * scan.D * 3 := by
  apply CollarScan.sum_card_state_designatedSplitIncidence_le_domainGraph
    target_nonempty scan rfl rfl history (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ambient_rows
  · intro x
    exact (Finset.card_filter_le _ _).trans (by simp)
  · exact clearance

private theorem depth_eq_first (x : Site domain) : scan.depth x = x.val.1 := by
  rcases site_cases x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [scan, target, ambientDepth, ambientSupDistance,
      p0, p12, p13, p14, p108, p109, p110, p1000, p1001]

private theorem second_zero (x : Site domain) : x.val.2 = 0 := by
  rcases site_cases x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem depth_injective : Function.Injective scan.depth := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact (depth_eq_first x).symm.trans (h.trans (depth_eq_first y))
  · rw [second_zero, second_zero]

private theorem row_anchor (i : Fin 3) :
    depthRow scan.depth (scan.depth (scan.anchor i)) = [scan.anchor i] := by
  have hf : (Finset.univ.filter fun x ↦ scan.depth x = scan.depth (scan.anchor i)) =
      {scan.anchor i} := by
    ext x
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      using depth_injective.eq_iff
  simp only [depthRow, hf, Finset.toList_singleton]

private theorem first_fill_slot (g : Fin 2) :
    fillSlot scan.A scan.depth scan.n (scan.lower g 0) (scan.upper g 0) false 0 =
      some (scan.anchor (if g = 0 then 0 else 2)) := by
  have h13 : depthRow scan.depth 13 = [p13] := by
    simpa [scan, target, ambientDepth, ambientSupDistance, p13] using row_anchor 0
  have h109 : depthRow scan.depth 109 = [p109] := by
    simpa [scan, target, ambientDepth, ambientSupDistance, p109] using row_anchor 2
  fin_cases g <;>
    norm_num [fillSlot, initialFront, orientedRow, CollarScan.lower, CollarScan.upper,
      h13, h109, scan, p13, p109, p1001, site_eq_iff]

private theorem old_state (g : Fin 2) :
    scan.oldChargeState history g =
      assign (scan.state history g) false {scan.anchor (if g = 0 then 0 else 2)} := by
  unfold CollarScan.oldChargeState fill
  norm_num only [history, fillSide, fillCount]
  simp only [decide_false, Bool.false_eq_true, ↓reduceIte, Fin.val_zero]
  rw [first_fill_slot]

private theorem old_split (g : Fin 2) :
    scan.designatedSplitIncidence (scan.oldChargeState history g)
      192 (if g = 0 then 0 else 2) false := by
  rw [CollarScan.designatedSplitIncidence, designated_eq_ball, old_state]
  fin_cases g
  · constructor
    · refine ⟨p13, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [CollarScan.ball]
      · norm_num [receiving, assign, CollarScan.state, CollarScan.bandState, history,
          initialPartition, CollarScan.lower, CollarScan.upper, scan, target,
          ambientDepth, ambientSupDistance, p13, p1001, site_eq_iff]
    · refine ⟨p14, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq,
          domainGraph, p13, p14]
      · norm_num [middle, assign, CollarScan.state, CollarScan.bandState, history,
          initialPartition, CollarScan.lower, CollarScan.upper, scan, target,
          ambientDepth, ambientSupDistance, p13, p14, p1001, site_eq_iff]
  · constructor
    · refine ⟨p109, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [CollarScan.ball]
      · norm_num [receiving, assign, CollarScan.state, CollarScan.bandState, history,
          initialPartition, CollarScan.lower, CollarScan.upper, scan, target,
          ambientDepth, ambientSupDistance, p109, p1001, site_eq_iff]
    · refine ⟨p110, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [CollarScan.ball, SimpleGraph.edist_le_one_iff_adj_or_eq,
          domainGraph, p109, p110]
      · norm_num [middle, assign, CollarScan.state, CollarScan.bandState, history,
          initialPartition, CollarScan.lower, CollarScan.upper, scan, target,
          ambientDepth, ambientSupDistance, p109, p110, p1001, site_eq_iff]

-- The pre-charge theorem is nonvacuous in both physical bands after the fill.
example (g : Fin 2) : IsTerminalSplit (scan.oldChargeState history)
    (designatedSupport scan.graph (scan.truncationSet 192) scan.r₀
      (scan.anchor (if g = 0 then 0 else 2))) g false := by
  exact CollarScan.old_designatedSplitIncidence_isTerminalSplit_domainGraph
    target_nonempty scan rfl rfl history (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ambient_rows clearance
    g false _ (old_split g)

open Classical in
example : (∑ g : Fin scan.K, ∑ side : Bool,
    (Finset.univ.filter fun i ↦
      scan.designatedSplitIncidence (scan.oldChargeState history g) 192 i side).card) ≤
    10 * scan.K * scan.n * scan.D * 3 := by
  apply CollarScan.sum_card_old_designatedSplitIncidence_le_domainGraph
    target_nonempty scan rfl rfl history (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ambient_rows
  · intro x
    exact (Finset.card_filter_le _ _).trans (by simp)
  · exact clearance

end
end TNLeanTest.ActualBandGeometry
