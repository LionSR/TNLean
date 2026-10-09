/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ExpectedMoveCost
import TNLean.PEPS.AreaLaw.CrossingBudget

/-!
# Actual sampling of the truncated designated supports

The original compact truncation set is the chosen color inside the depth-L
collar. The actual old middle lies in this set. A designated support crossing
that middle therefore equals the fixed-radius charge ball by the established
variable-radius truncation theorem. This identifies the selected move with the
unassigned part of the designated support, rather than assuming that every
truncated support has the base radius.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 225–233 and 331–337, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- The actual compact set used for truncation: the chosen color through depth `L`. -/
def truncationSet (L : ℕ) : Finset V := S.A.filter fun x ↦ S.depth x ≤ L

/-- The actual old middle is contained in the original compact truncation set. -/
theorem middle_subset_truncationSet {k L : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) :
    middle (S.oldChargeState h g) ⊆ S.truncationSet L := by
  intro x hx
  have hn := (Finset.mem_filter.mp hx).2
  have hA := (initial_middle_depth S.A S.depth _ _
    (S.oldChargeState_initial_none h g x hn) false).1
  exact Finset.mem_filter.mpr ⟨hA,
    (Finset.mem_Icc.mp (S.oldChargeState_depth_bounds h g hL x hn)).2⟩

/-- Splitting designated supports, including the variable-radius truncation case,
are exactly the base-radius balls that the actual charge lottery selects. -/
theorem designatedSupport_eq_ball_of_split {k L : ℕ} (h : History S.K S.m S.M k)
    (g : Fin S.K) (side : Bool) (i : I) (hL : 8 * S.K * S.m ≤ L)
    (hsplit :
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving (S.oldChargeState h g) side).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        middle (S.oldChargeState h g)).Nonempty) :
    designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) = S.ball i := by
  classical
  have hcross : i ∈ crossingLabels S.graph (S.truncationSet L) S.r₀ S.anchor
      (middle (S.oldChargeState h g)) := by
    obtain ⟨x, hx⟩ := hsplit.2
    obtain ⟨y, hy⟩ := hsplit.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩,
      y, (Finset.mem_inter.mp hy).1, ?_⟩
    have hs := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
    simp [middle, hs]
  have heq := (truncationRadius_eq_of_mem_crossingLabels
    (S.middle_subset_truncationSet h g hL) hcross).2.2
  simpa only [QuantumCircuit.graphBall, ball] using heq

/-- Each splitting truncated designated support is sampled by the actual finite
history with probability `1/(2M) ≥ c/(nD)`, and the extended history removes its
exact old unassigned part. The probability is classical, before state transport. -/
theorem good_designated_split_sampling_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (side : Bool) (i : I)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hgood : S.IsGoodOldHistory h)
    (hsplit :
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        receiving (S.oldChargeState h g) side).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
        middle (S.oldChargeState h g)).Nonempty) :
    ∃! slot : Fin S.M,
      S.selected g (h.1 g) (k + 1) (side, slot) = some i ∧
      (∀ c : ChargeChoices S.K S.M, c g = (side, slot) →
        middle (S.oldChargeState h g) \ middle (S.state (extendHistory h c) g) =
          designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i) ∩
            middle (S.oldChargeState h g)) ∧
      (∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0) =
        1 / (2 * (S.M : ℝ)) ∧
      0 < 1 / (2 * (S.C₁ + 1)) ∧
      (1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D) ≤
        ∑ c : ChargeChoices S.K S.M, if c g = (side, slot) then chargeWeight c else 0 := by
  have heq := S.designatedSupport_eq_ball_of_split h g side i hL hsplit
  simpa only [heq] using good_split_sampling_domainGraph hT S hgraph hdepth h g side i
    hn hm hk hr hD hDpos hL hC hrows hmult hclear hgood (by simpa only [heq] using hsplit)

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
