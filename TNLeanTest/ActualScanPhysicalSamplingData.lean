/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ExpectedMoveCost
import TNLean.PEPS.AreaLaw.Scan.DesignatedDilution

/-!
# Shared physical entropy-sampling geometry

The original six-site sampling fixture, with all its numerical margins,
ambient rows, real cut, good old history and split designated support.
Definitions are shared only among regression modules; the physical construction
and every proof are preserved from the original sampling regression.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

namespace TNLeanTest.ActualScanPhysicalSampling

noncomputable section

/-- The six-site induced lattice domain, including a genuine cut edge. -/
def domain : Finset (ℤ × ℤ) :=
  {(0, 0), (33, 0), (34, 0), (1000, 0), (1001, 0), (5000, 0)}

/-- Two target sites on opposite sides of the cut. -/
def target : Finset (ℤ × ℤ) := {(0, 0), (5000, 0)}

/-- The target contains the origin. -/
theorem target_nonempty : target.Nonempty := by simp [target]

/-- The origin target site inside the physical region. -/
def p0 : Site domain := ⟨(0, 0), by simp [domain]⟩
private def p33 : Site domain := ⟨(33, 0), by simp [domain]⟩
private def p34 : Site domain := ⟨(34, 0), by simp [domain]⟩
private def p1000 : Site domain := ⟨(1000, 0), by simp [domain]⟩
private def p1001 : Site domain := ⟨(1001, 0), by simp [domain]⟩
/-- The target site outside the physical region. -/
def p5000 : Site domain := ⟨(5000, 0), by simp [domain]⟩

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

/-- The scanner with source-compatible margins and an actual radius-one split. -/
abbrev scan : CollarScan (Site domain) (Fin 1) where
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

/-- The initial history with zero offset and no previous charges. -/
def history : History scan.K scan.m scan.M 0 :=
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

/-- The actual old history obeys both receiving-side lead bounds. -/
theorem good_history : scan.IsGoodOldHistory history := by
  intro g side x hx hs
  have hg : g = 0 := Fin.eq_zero g
  subst g
  rw [old_state] at hs
  rcases site_cases x with rfl | rfl | rfl | rfl | rfl | rfl <;> cases side <;>
    norm_num [scan, p0, p33, p34, p1000, p1001, p5000, site_eq_iff, target, ambientDepth,
      ambientSupDistance, orientedDepth, CollarScan.front, nominalFront,
      initialFront, fillCount, CollarScan.lower, CollarScan.upper, history] at *

/-- The radius-one anchor ball meets the actual near side and middle. -/
theorem ball_split :
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

/-- All ambient depth rows through the chosen truncation scale obey the row bound. -/
theorem ambient_rows (d : ℕ) (_hd : 1 ≤ d) (hdL : d ≤ 256) :
    (ambientDilation target d \ ambientDilation target (d - 1)).card ≤ scan.n := by
  calc
    _ ≤ (ambientDilation target d).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ (2 * d + 1) ^ 2 * target.card := Geometry.card_ambientDilation_le target d
    _ ≤ (2 * 256 + 1) ^ 2 * 2 := by
      have ht : target.card = 2 := by norm_num [target]
      rw [ht]
      exact Nat.mul_le_mul_right 2 (Nat.pow_le_pow_left (by omega) 2)
    _ ≤ scan.n := by norm_num

/-- The cut has exactly the two endpoints of the distant adjacent pair. -/
theorem boundary_endpoints :
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

/-- Both targets have the required clearance from the actual cut endpoints. -/
theorem clearance : ∀ t ∈ target,
    ∀ z ∈ Geometry.boundaryEndpoints domain scan.A,
      ((2 * 256 + 10 * scan.r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
  rw [boundary_endpoints]
  simp only [target, Finset.mem_insert, Finset.mem_singleton]
  rintro t (rfl | rfl) z (rfl | rfl) <;> norm_num [scan, ambientSupDistance]

/-- The actual truncated designated support equals the splitting radius-one ball. -/
theorem designated_ball :
    designatedSupport scan.graph (scan.truncationSet 256) scan.r₀ (scan.anchor 0) =
      scan.ball 0 := by
  have ha : scan.anchor 0 ∈ scan.truncationSet 256 := by
    norm_num [CollarScan.truncationSet, scan, p33, ambientDepth, target, ambientSupDistance]
  have hd : setDist scan.graph (scan.truncationSet 256) (scan.anchor 0) = 0 := by
    apply le_antisymm _ zero_le
    exact (Finset.inf_le ha).trans (by simp)
  simp [designatedSupport, hd, truncationRadius, QuantumCircuit.graphBall, CollarScan.ball]


end

end TNLeanTest.ActualScanPhysicalSampling
