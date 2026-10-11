/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryTimeUnion
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# A physical three-charge bad history

The actual domain contains a path at depths 32–39 and a distant genuine cut
edge. Three successive radius-one charges at 34, 36, and 38 propagate the
near side from its first fill at 33 to 39. The front remains 33, so the lead
six exceeds the lookahead half-width four. All moves use the actual labelled
candidate slots and domain graph, with no supplied ancestry certificate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 286–329, at `openai/math@adc7f124`.
-/

set_option autoImplicit false

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open scoped BigOperators

namespace TNLeanTest.PhysicalBadHistory

noncomputable section

private def domain : Finset (ℤ × ℤ) :=
  {(0, 0), (32, 0), (33, 0), (34, 0), (35, 0), (36, 0), (37, 0),
    (38, 0), (39, 0), (2000, 0), (2001, 0)}

private def target : Finset (ℤ × ℤ) := {(0, 0)}

private theorem target_nonempty : target.Nonempty := by simp [target]

private def point (a : ℤ) (ha : a = 0 ∨ 32 ≤ a ∧ a ≤ 39 ∨ a = 2000 ∨ a = 2001) :
    Site domain := ⟨(a, 0), by
  simp only [domain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true]
  omega⟩

private theorem coordinates (x : Site domain) :
    x.val.2 = 0 ∧
      (x.val.1 = 0 ∨ 32 ≤ x.val.1 ∧ x.val.1 ≤ 39 ∨
        x.val.1 = 2000 ∨ x.val.1 = 2001) := by
  classical
  have hx := x.property
  simp only [domain, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at hx
  omega

private def scan : CollarScan (Site domain) (Fin 3) where
  graph := domainGraph domain
  A := Finset.univ.filter fun x ↦ x.val.1 ≤ 2000
  depth := fun x ↦ ambientDepth target target_nonempty x.val
  anchor := fun i ↦ point (34 + 2 * i.val) (by omega)
  n := 600000
  m := 32
  K := 1
  D := 8
  r₀ := 1
  C₁ := 1000

private theorem depth_eq (x : Site domain) : scan.depth x = x.val.1 := by
  classical
  have hx := coordinates x
  change ambientDepth target target_nonempty x.val = x.val.1
  simp [ambientDepth, target, ambientSupDistance, hx.1, abs_of_nonneg (by omega : 0 ≤ x.val.1)]
  omega

private theorem point_eq_iff (x y : Site domain) : x = y ↔ x.val.1 = y.val.1 := by
  classical
  constructor
  · exact fun h ↦ congrArg (fun z : Site domain ↦ z.val.1) h
  · intro h
    apply Subtype.ext
    exact Prod.ext h ((coordinates x).1.trans (coordinates y).1.symm)

private theorem ball_mem (i : Fin 3) (x : Site domain) :
    x ∈ scan.ball i ↔ 33 + 2 * (i.val : ℤ) ≤ x.val.1 ∧ x.val.1 ≤ 35 + 2 * i.val := by
  classical
  simp only [CollarScan.ball, Finset.mem_filter, Finset.mem_univ, true_and]
  change (domainGraph domain).edist (point (34 + 2 * i.val) (by omega)) x ≤ (1 : ℕ∞) ↔ _
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  simp only [domainGraph, point_eq_iff]
  simp only [point, (coordinates x).1]
  simp only [true_and, zero_add, one_ne_zero, or_self, and_false, or_false]
  omega

private def stage (b : ℤ) : PhysicalPartition (Site domain) :=
  fun x ↦ if x.val.1 ≤ b then some false else if 2000 ≤ x.val.1 then some true else none

private theorem depth_row (a : ℤ) (ha : 32 ≤ a ∧ a ≤ 39) :
    depthRow scan.depth a = [point a (by omega)] := by
  classical
  have hf : (Finset.univ.filter fun x ↦ scan.depth x = a) = {point a (by omega)} := by
    classical
    ext x
    simp [depth_eq, point_eq_iff, point]
  unfold depthRow
  rw [hf]
  simp

private theorem depth_row_far : depthRow scan.depth 160 = [] := by
  classical
  have hf : (Finset.univ.filter fun x ↦ scan.depth x = 160) = ∅ := by
    classical
    ext x
    have hx := (coordinates x).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, depth_eq, Finset.notMem_empty,
      iff_false]
    omega
  unfold depthRow
  rw [hf]
  simp

private theorem initial_state :
    initialPartition scan.A scan.depth (scan.lower 0 0) (scan.upper 0 0) = stage 32 := by
  classical
  funext x
  have hx := coordinates x
  simp only [initialPartition, scan, Finset.mem_filter, Finset.mem_univ, true_and,
    CollarScan.lower, CollarScan.upper, stage]
  change (if ¬x.val.1 ≤ 2000 then some true else
    if scan.depth x ≤ 32 then some false else if 160 < scan.depth x then some true else none) = _
  rw [depth_eq]
  split_ifs <;> simp_all <;> omega

private theorem first_fill :
    fill scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0) 0 (stage 32) = stage 33 := by
  classical
  have hs : fillSlot scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0)
      (fillSide 0) (fillCount 0 (fillSide 0)) = some (point 33 (by omega)) := by
    classical
    change ((depthRow scan.depth 33)[0]?).filter (fun x ↦ x ∈ scan.A) = _
    rw [depth_row 33 (by omega)]
    norm_num [scan, point]
  simp only [fill, hs]
  funext x
  simp only [assign, Finset.mem_singleton, point_eq_iff, point, stage, fillSide]
  split_ifs <;> simp_all <;> omega

private theorem later_fill (k : Fin 2) (σ : PhysicalPartition (Site domain)) :
    fill scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0) (k.val + 1) σ = σ := by
  classical
  have hs : fillSlot scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0)
      (fillSide (k.val + 1)) (fillCount (k.val + 1) (fillSide (k.val + 1))) = none := by
    classical
    fin_cases k
    · change ((depthRow scan.depth 160)[0]?).filter (fun x ↦ x ∈ scan.A) = none
      rw [depth_row_far]
      rfl
    · change ((depthRow scan.depth 33)[1]?).filter (fun x ↦ x ∈ scan.A) = none
      rw [depth_row 33 (by omega)]
      rfl
  simp [fill, hs]

private theorem charge_stage (i : Fin 3) :
    charge (stage (33 + 2 * i.val)) false (scan.ball i) = stage (35 + 2 * i.val) := by
  classical
  have hs : (scan.ball i ∩ receiving (stage (33 + 2 * i.val)) false).Nonempty ∧
      (scan.ball i ∩ middle (stage (33 + 2 * i.val))).Nonempty := by
    classical
    constructor
    · refine ⟨point (33 + 2 * i.val) (by omega), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [ball_mem, point]
      · simp [receiving, stage, point]
    · refine ⟨point (34 + 2 * i.val) (by omega), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [ball_mem, point]
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change (if 34 + 2 * (i.val : ℤ) ≤ 33 + 2 * i.val then some false
          else if (2000 : ℤ) ≤ 34 + 2 * i.val then some true else none) = none
        split_ifs <;> simp_all
        omega
  rw [charge, ite_eq_left hs]
  funext x
  simp only [assign, ball_mem, stage]
  split_ifs <;> simp_all <;> omega

private theorem capacity : 3 ≤ scan.M := by
  classical
  norm_num [CollarScan.M, chargeSlotCount, scan]

private theorem occupied_slot (i : Fin 3) :
    ∃ slot : Fin scan.M, scan.selected 0 0 (i.val + 1) (false, slot) = some i := by
  classical
  apply ExistsUnique.exists
  change ∃! slot : Fin scan.M, paddedChargeSlot
    (orderedChargeCandidates (orientedDepth scan.depth false) scan.anchor
      (scan.front 0 0 (i.val + 1) false - scan.r₀)
      (scan.front 0 0 (i.val + 1) false + scan.D)) scan.M slot = some i
  apply existsUnique_orderedChargeSlot
  · exact (Finset.card_filter_le _ _).trans (by simpa using capacity)
  · change scan.front 0 0 (i.val + 1) false - 1 ≤ scan.depth (scan.anchor i) ∧
      scan.depth (scan.anchor i) ≤ scan.front 0 0 (i.val + 1) false + 8
    rw [depth_eq]
    fin_cases i <;> norm_num [CollarScan.front, nominalFront, initialFront, fillCount,
      CollarScan.lower, CollarScan.upper, scan, point]

private def slot (i : Fin 3) : Fin scan.M := (occupied_slot i).choose

private theorem selected_slot (i : Fin 3) :
    scan.selected 0 0 (i.val + 1) (false, slot i) = some i :=
  (occupied_slot i).choose_spec

private def choices (t : ℕ) : Bool × Fin scan.M :=
  if ht : t < 3 then (false, slot ⟨t, ht⟩) else (false, slot 0)

private theorem selected_step (i : Fin 3) (σ : PhysicalPartition (Site domain)) :
    scan.chargeStep 0 0 (i.val + 1) (false, slot i) σ = charge σ false (scan.ball i) := by
  unfold CollarScan.chargeStep
  rw [selected_slot]

private theorem state_three :
    scan.bandState 0 0 3 (fun j ↦ choices j) = stage 39 := by
  classical
  have hs0 := selected_step 0
  have hs1 := selected_step 1
  have hs2 := selected_step 2
  change ∀ σ, scan.chargeStep 0 0 1 (false, slot 0) σ = _ at hs0
  change ∀ σ, scan.chargeStep 0 0 2 (false, slot 1) σ = _ at hs1
  change ∀ σ, scan.chargeStep 0 0 3 (false, slot 2) σ = _ at hs2
  have hc0 := charge_stage 0
  have hc1 := charge_stage 1
  have hc2 := charge_stage 2
  change charge (stage 33) false (scan.ball 0) = stage 35 at hc0
  change charge (stage 35) false (scan.ball 1) = stage 37 at hc1
  change charge (stage 37) false (scan.ball 2) = stage 39 at hc2
  simp only [CollarScan.bandState, CollarScan.pairStep]
  rw [initial_state, first_fill]
  change scan.chargeStep 0 0 3 (false, slot 2)
    (fill scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0) 2
      (scan.chargeStep 0 0 2 (false, slot 1)
        (fill scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0) 1
          (scan.chargeStep 0 0 1 (false, slot 0) (stage 33))))) = _
  have hf0 := later_fill 0
  have hf1 := later_fill 1
  change ∀ σ, fill scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0) 1 σ = σ at hf0
  change ∀ σ, fill scan.A scan.depth scan.n (scan.lower 0 0) (scan.upper 0 0) 2 σ = σ at hf1
  rw [hs0, hc0, hf0, hs1, hc1, hf1, hs2, hc2]


private theorem boundary_endpoints :
    Geometry.boundaryEndpoints domain scan.A = {(2000, 0), (2001, 0)} := by
  classical
  classical
  have hcut : edgeBoundary domain scan.A =
      {s(point 2000 (by omega), point 2001 (by omega))} := by
    classical
    ext e
    constructor
    · intro he
      obtain ⟨he, x, hx, y, hy, rfl⟩ := Finset.mem_filter.mp he
      have hadj : (domainGraph domain).Adj x y := by
        classical
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      have hxc := coordinates x
      have hyc := coordinates y
      simp only [scan, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      simp only [domainGraph, hxc.1, hyc.1] at hadj
      have hxeq : x = point 2000 (by omega) := point_eq_iff x _ |>.mpr (by
        simp only [point]
        omega)
      have hyeq : y = point 2001 (by omega) := point_eq_iff y _ |>.mpr (by
        simp only [point]
        omega)
      simp [hxeq, hyeq]
    · intro he
      have heq := Finset.mem_singleton.mp he
      subst e
      refine Finset.mem_filter.mpr ⟨?_, point 2000 (by omega), ?_,
        point 2001 (by omega), ?_, rfl⟩
      · apply SimpleGraph.mem_edgeFinset.mpr
        change (domainGraph domain).Adj (point 2000 (by omega)) (point 2001 (by omega))
        norm_num [domainGraph, point]
      · norm_num [scan, point]
      · norm_num [scan, point]
  rw [Geometry.boundaryEndpoints, hcut]
  simp [Sym2.toFinset_mk_eq, point]

private theorem clearance : ∀ t ∈ target,
    ∀ z ∈ Geometry.boundaryEndpoints domain scan.A,
      ((2 * 256 + 10 * scan.r₀ : ℕ) : ℤ) < ambientSupDistance t z := by
  classical
  rw [boundary_endpoints]
  simp only [target, Finset.mem_insert, Finset.mem_singleton]
  rintro t rfl z (rfl | rfl) <;> norm_num [scan, ambientSupDistance]

private theorem ambient_rows (d : ℕ) (_hd : 1 ≤ d) (hdL : d ≤ 256) :
    (ambientDilation target d \ ambientDilation target (d - 1)).card ≤ scan.n := by
  classical
  calc
    _ ≤ (ambientDilation target d).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ (2 * d + 1) ^ 2 * target.card := Geometry.card_ambientDilation_le target d
    _ ≤ (2 * 256 + 1) ^ 2 * 1 := by
      classical
      have ht : target.card = 1 := by simp [target]
      rw [ht]
      exact Nat.mul_le_mul_right 1 (Nat.pow_le_pow_left (by omega) 2)
    _ ≤ scan.n := by norm_num [scan]

-- The evaluated third charge creates a genuinely bad site in the chosen color.
example : scan.bandState 0 0 3 (fun j ↦ choices j) (point 39 (by omega)) = some false ∧
    2 * scan.front 0 0 3 false + scan.D <
      2 * orientedDepth scan.depth false (point 39 (by omega)) := by
  classical
  rw [state_three]
  norm_num [stage, point, orientedDepth, depth_eq, CollarScan.front, nominalFront,
    initialFront, fillCount, CollarScan.lower, CollarScan.upper, scan,
    ambientDepth, target, ambientSupDistance]

-- The physical theorem derives a long ancestry from that actual evaluated state.
example : ∃ events, scan.ChargeAncestry 0 0 choices false 3 (point 39 (by omega)) events ∧
    events ≠ [] ∧ (scan.D : ℤ) < 4 * scan.r₀ * events.length ∧
    ∀ e ∈ events, (3 : ℤ) - (e.1 + 1) ≤
      4 * scan.n * ((scan.r₀ : ℤ) * events.length + 1) := by
  classical
  apply CollarScan.bad_bandState_has_long_chargeAncestry_domainGraph target_nonempty
    scan rfl rfl (⟨0, by norm_num [scan]⟩ : Fin scan.K)
    (⟨0, by norm_num [scan]⟩ : Fin scan.m) choices (L := 256)
    (by norm_num [scan]) (by norm_num [scan]) clearance 3 false (point 39 (by omega))
  · norm_num [scan, point]
  · change scan.bandState 0 0 3 (fun j ↦ choices j) (point 39 _) = some false
    rw [state_three]
    norm_num [stage, point]
  · norm_num [orientedDepth, depth_eq, CollarScan.front, nominalFront,
      initialFront, fillCount, CollarScan.lower, CollarScan.upper, scan, point,
      ambientDepth, target, ambientSupDistance]

private theorem multiplicity (y : Site domain) :
    (Finset.univ.filter fun i ↦ scan.anchor i = y).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hij := congrArg (fun z : Site domain ↦ z.val.1) (hi'.trans hj'.symm)
  change 34 + 2 * (i.val : ℤ) = 34 + 2 * (j.val : ℤ) at hij
  apply Fin.ext
  omega

private theorem endpoint_tail :
    scan.badEndpointTail 3 1 = (13 / 9600000000 : ℝ) ^ 3 := by
  unfold CollarScan.badEndpointTail
  rw [Finset.sum_filter]
  norm_num [Finset.sum_range_succ, recentChargeTimes, scan, CollarScan.M, chargeSlotCount]

open Classical in
example : (∑ c : Fin 3 → ChargeChoices scan.K scan.M,
    if scan.IsBadBandEndpoint (fun _ ↦ ⟨0, by norm_num [scan]⟩)
      ⟨0, by norm_num [scan]⟩ false (point 39 (by omega)) c
    then ((1 / (2 * (scan.M : ℝ))) ^ scan.K) ^ 3 else 0) < 1 := by
  have hb := CollarScan.sum_chargePathWeight_bad_endpoint_domainGraph_le target_nonempty
    scan rfl rfl (k := 3) (L := 256) (μ := 1)
    (fun _ ↦ ⟨0, by norm_num [scan]⟩) ⟨0, by norm_num [scan]⟩ false
    (point 39 (by omega)) (by norm_num [scan, point]) (by norm_num [scan])
    (lt_of_lt_of_le (by decide : 0 < 3) capacity) (by norm_num [scan]) clearance multiplicity
  rw [endpoint_tail] at hb
  exact hb.trans_lt (by norm_num)


-- The same physical model exercises the union over every prefix of three pairs.
open Classical in
example : (∑ h : History scan.K scan.m scan.M 3,
    if ¬ scan.IsGoodThrough h then historyWeight h else 0) < 1 := by
  have hb := CollarScan.sum_historyWeight_bad_through_domainGraph_le target_nonempty
    scan rfl rfl (N := 3) (L := 256) (μ := 1)
    (by norm_num [scan]) (by norm_num [scan])
    (lt_of_lt_of_le (by decide : 0 < 3) capacity)
    (by norm_num [scan]) clearance ambient_rows multiplicity
  apply hb.trans_lt
  unfold CollarScan.badEndpointTail
  simp only [Finset.sum_filter]
  norm_num [Fin.sum_univ_succ, Finset.sum_range_succ, recentChargeTimes,
    scan, target, CollarScan.M, chargeSlotCount]

end
end TNLeanTest.PhysicalBadHistory
