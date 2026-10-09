/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.DesignatedSampling

/-!
# Expected move cost for truncated designated supports

A splitting designated support gives a splitting ball with the same old middle
part. The nonnegative sum over designated-support incidences is therefore bounded
by the sum over ball incidences, and hence by the expected cost of the actual
charge moves. Incidences retain their band, side, and interaction label; neither
equal anchors nor participation in several bands identifies them.

This is a classical finite expectation inequality. No identification of its
costs with quantum entropy quantities is asserted.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 225–233 and 331–337, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- Side-label incidences whose truncated designated support meets both the
receiving side and the old middle (`08-scanner.tex`, lines 225–233 and 331–337). -/
noncomputable def designatedSplitIncidences (L : ℕ) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) : Finset (Bool × I) :=
  Finset.univ.filter fun p ↦
    (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor p.2) ∩
      receiving (S.oldChargeState h g) p.1).Nonempty ∧
    (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor p.2) ∩
      middle (S.oldChargeState h g)).Nonempty

@[simp]
theorem mem_designatedSplitIncidences (L : ℕ) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (p : Bool × I) :
    p ∈ S.designatedSplitIncidences L h g ↔
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor p.2) ∩
        receiving (S.oldChargeState h g) p.1).Nonempty ∧
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor p.2) ∩
        middle (S.oldChargeState h g)).Nonempty := by
  classical
  simp [designatedSplitIncidences]

/-- Every splitting designated support is a splitting charge ball
(`08-scanner.tex`, lines 225–233 and 331–337). -/
theorem designatedSplitIncidences_subset_splitIncidences (L : ℕ) {k : ℕ}
    (h : History S.K S.m S.M k) (g : Fin S.K) (hL : 8 * S.K * S.m ≤ L) :
    S.designatedSplitIncidences L h g ⊆ S.splitIncidences h g := by
  intro p hp
  have hsplit := (S.mem_designatedSplitIncidences L h g p).mp hp
  have heq := S.designatedSupport_eq_ball_of_split h g p.1 p.2 hL hsplit
  exact (S.mem_splitIncidences h g p).mpr (by simpa only [heq] using hsplit)

/-- The sum of costs over all splitting band-side-label incidences of the
truncated designated supports (`08-scanner.tex`, lines 331–337). -/
noncomputable def designatedSplitIncidenceCost (L : ℕ) {k : ℕ}
    (h : History S.K S.m S.M k) (cost : Fin S.K → Bool → Finset V → ℝ) : ℝ :=
  ∑ g, ∑ p ∈ S.designatedSplitIncidences L h g,
    cost g p.1 (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor p.2) ∩
      middle (S.oldChargeState h g))

/-- Nonnegative designated-support incidence costs are bounded by the ball
incidence costs, with identical old middle parts on the smaller index set
(`08-scanner.tex`, lines 225–233 and 331–337). -/
theorem designatedSplitIncidenceCost_le_splitIncidenceCost (L : ℕ) {k : ℕ}
    (h : History S.K S.m S.M k) (cost : Fin S.K → Bool → Finset V → ℝ)
    (hL : 8 * S.K * S.m ≤ L) (hcost : ∀ g side B, 0 ≤ cost g side B) :
    S.designatedSplitIncidenceCost L h cost ≤ S.splitIncidenceCost h cost := by
  classical
  unfold designatedSplitIncidenceCost splitIncidenceCost
  apply Finset.sum_le_sum
  intro g _
  calc
    _ = ∑ p ∈ S.designatedSplitIncidences L h g,
        cost g p.1 (S.ball p.2 ∩ middle (S.oldChargeState h g)) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [S.designatedSupport_eq_ball_of_split h g p.1 p.2 hL
        ((S.mem_designatedSplitIncidences L h g p).mp hp)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (S.designatedSplitIncidences_subset_splitIncidences L h g hL)
      (fun p _ _ ↦ hcost g p.1 _)

/-- In a good actual history, the expected side-dependent cost of the charge
moves dominates `c / (nD)` times the truncated designated-support incidence
cost, for `c = 1 / (2(C₁ + 1)) > 0`. The physical geometry and multiplicity
bounds supply the sampling estimate (`08-scanner.tex`, lines 331–337). -/
theorem good_designatedSplitIncidenceCost_le_expected_chargeMoveCost_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val) {k L μ : ℕ}
    (h : History S.K S.m S.M k) (cost : Fin S.K → Bool → Finset (Site Λ) → ℝ)
    (hcost : ∀ g side B, 0 ≤ cost g side B)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hk : k + 1 ≤ S.n * S.m)
    (hr : 2 * S.r₀ ≤ S.D) (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hgood : S.IsGoodOldHistory h) :
    0 < 1 / (2 * (S.C₁ + 1)) ∧
      ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)) *
          S.designatedSplitIncidenceCost L h cost ≤
        ∑ c : ChargeChoices S.K S.M, chargeWeight c * S.chargeMoveCost h cost c := by
  have hbound := good_splitIncidenceCost_le_expected_chargeMoveCost_domainGraph
    hT S hgraph hdepth h cost hcost hn hm hk hr hD hDpos hL hC hrows hmult hclear hgood
  refine ⟨hbound.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left
    (S.designatedSplitIncidenceCost_le_splitIncidenceCost L h cost hL hcost)
    (div_nonneg hbound.1.le (by positivity))).trans hbound.2

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
