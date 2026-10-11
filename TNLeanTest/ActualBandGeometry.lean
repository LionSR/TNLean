/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLeanTest.ActualBandGeometryData
import TNLean.PEPS.AreaLaw.Scan.SplitCounting
import TNLean.PEPS.AreaLaw.Scan.StatusCutBounds

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
open TNLeanTest.ActualBandGeometryData
open scoped symmDiff

namespace TNLeanTest.ActualBandGeometry
noncomputable section

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

-- The completed physical theorem applies uniformly to every history in both
-- genuine bands, not just to an empty or certificate-supplied geometry.
example {k : ℕ} (h : History scan.K scan.m scan.M k) (hk : k ≤ scan.n * scan.m)
    (g : Fin scan.K) :
    ((positiveNear scan.depth (scan.state h g)) ∆ positiveDepthPrefix scan.A scan.depth
      (scan.front g (h.1 g) k false - 1)).card ≤ 3 * scan.n * scan.D := by
  exact (CollarScan.state_prefix_approximation_domainGraph target_nonempty scan rfl rfl
    h g (by norm_num) hk (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : 8 * scan.K * scan.m ≤ 192) ambient_rows).2.2.2.2.1

example {k : ℕ} (h : History scan.K scan.m scan.M k) (hk : k + 1 ≤ scan.n * scan.m)
    (g : Fin scan.K) :
    ((positiveNearMiddle scan.depth (scan.oldChargeState h g)) ∆
      positiveDepthPrefix scan.A scan.depth (-scan.front g (h.1 g) (k + 1) true)).card ≤
        3 * scan.n * scan.D := by
  exact (CollarScan.oldChargeState_prefix_approximation_domainGraph
    target_nonempty scan rfl rfl h g (by norm_num) hk (by norm_num) (by norm_num)
    (by norm_num) (by norm_num : 8 * scan.K * scan.m ≤ 192) ambient_rows).2.2.2.2.2

-- A consumed part of the current row is genuinely outside the whole-row
-- comparison prefix. The additive one-row allowance is therefore necessary.
example : p13 ∈ positiveNear scan.depth (scan.oldChargeState history 0) ∧
    p13 ∉ positiveDepthPrefix scan.A scan.depth (scan.front 0 0 1 false - 1) := by
  rw [old_state]
  norm_num [positiveNear, positiveDepthPrefix, receiving, assign, CollarScan.state,
    CollarScan.bandState, history, initialPartition, scan, target, ambientDepth,
    ambientSupDistance, CollarScan.lower, CollarScan.upper, CollarScan.front,
    nominalFront, initialFront, fillCount, p13, p1001, site_eq_iff]

-- Every numerical, ambient-row and genuine-cut clearance hypothesis is
-- discharged on this same two-band lattice fixture.
example (g : Fin scan.K) :
    (edgeBoundary domain (middle (scan.state history g))).card ≤ 40 * scan.n * scan.D := by
  exact (CollarScan.state_cut_bounds_domainGraph target_nonempty scan rfl rfl history g
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : 8 * scan.K * scan.m ≤ 192) ambient_rows clearance).2.2.1

example (g : Fin scan.K) :
    (edgeBoundary domain (receiving (scan.oldChargeState history g) true)).card ≤
      16 * scan.n * scan.D := by
  exact (CollarScan.oldChargeState_cut_bounds_domainGraph target_nonempty scan rfl rfl history g
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num : 8 * scan.K * scan.m ≤ 192) ambient_rows clearance).2.2.2.2


end
end TNLeanTest.ActualBandGeometry
