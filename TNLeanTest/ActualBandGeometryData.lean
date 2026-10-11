/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TerminalSplits

/-!
# Shared physical data for the two-band scanner regressions

The domain, target, graph, row bounds, actual cut clearance, and two genuine
splitting supports are checked once. Geometry, prefix, and support tests use
these same data; no scanner hypothesis is replaced by a supplied certificate.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

namespace TNLeanTest.ActualBandGeometryData
noncomputable section

/-- The shared two-band physical domain, including its genuine cut edge. -/
def domain : Finset (ℤ × ℤ) := {(0, 0), (12, 0), (13, 0), (14, 0), (108, 0), (109, 0),
    (110, 0), (1000, 0), (1001, 0)}
/-- The nonempty ambient target for the shared scan. -/
def target : Finset (ℤ × ℤ) := {(0, 0)}
/-- The target contains the origin. -/
theorem target_nonempty : target.Nonempty := by simp [target]
private def p0 : Site domain := ⟨(0, 0), by simp [domain]⟩
private def p12 : Site domain := ⟨(12, 0), by simp [domain]⟩
/-- The first band’s depth-thirteen anchor. -/
def p13 : Site domain := ⟨(13, 0), by simp [domain]⟩
private def p14 : Site domain := ⟨(14, 0), by simp [domain]⟩
private def p108 : Site domain := ⟨(108, 0), by simp [domain]⟩
private def p109 : Site domain := ⟨(109, 0), by simp [domain]⟩
private def p110 : Site domain := ⟨(110, 0), by simp [domain]⟩
private def p1000 : Site domain := ⟨(1000, 0), by simp [domain]⟩
/-- The exterior endpoint of the genuine cut edge. -/
def p1001 : Site domain := ⟨(1001, 0), by simp [domain]⟩
/-- Equality of physical sites is equality of their lattice coordinates. -/
theorem site_eq_iff (x y : Site domain) : x = y ↔ x.val = y.val :=
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

/-- The shared scanner with two separated windows and repeated anchor labels. -/
abbrev scan : CollarScan (Site domain) (Fin 3) where
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

/-- The initial history with zero offsets in both bands. -/
def history : History scan.K scan.m scan.M 0 := (fun _ ↦ 0, Fin.elim0)

/-- All relevant ambient depth rows obey the common padded row bound. -/
theorem ambient_rows (d : ℕ) (_hd : 1 ≤ d) (hdL : d ≤ 192) :
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

/-- The actual cut is farther from the target than the required source margin. -/
theorem clearance : ∀ t ∈ target,
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

/-- Both bands have an actual designated middle-side incidence initially. -/
theorem initial_split (g : Fin 2) :
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

/-- The first fill moves the selected band’s depth-thirteen or depth-109 anchor. -/
theorem old_state (g : Fin 2) :
    scan.oldChargeState history g =
      assign (scan.state history g) false {scan.anchor (if g = 0 then 0 else 2)} := by
  unfold CollarScan.oldChargeState fill
  norm_num only [history, fillSide, fillCount]
  simp only [decide_false, Bool.false_eq_true, ↓reduceIte, Fin.val_zero]
  rw [first_fill_slot]

/-- Both pre-charge statuses still have a genuine designated split after the first fill. -/
theorem old_split (g : Fin 2) :
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

end
end TNLeanTest.ActualBandGeometryData
