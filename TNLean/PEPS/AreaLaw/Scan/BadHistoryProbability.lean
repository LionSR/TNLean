/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AncestryCover
import TNLean.PEPS.AreaLaw.Scan.PhysicalChargeAncestry
import TNLean.PEPS.AreaLaw.Scan.SelectedChainProbability

/-!
# A finite bad-endpoint probability bound

For fixed initial offsets, an actual bad physical endpoint forces one of the
explicitly enumerated long charge paths. Each path fixes distinct independent
side-and-labelled-slot coordinates. Summing their probabilities gives a finite
binomial tail, with the actual square-lattice diamond count and anchor
multiplicity. Successful physical moves are never asserted independent.

This is a finite bound. The eventual inverse-power specialization, the union
over times and compact endpoints, and quantum transported weights are separate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 286–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

namespace CollarScan

/-- Badness of one actual completed-pair endpoint, conditional on all initial offsets. -/
def IsBadBandEndpoint {V : Type*} [Fintype V] [DecidableEq V]
    (S : CollarScan V I) {k : ℕ} (offsets : Fin S.K → Fin S.m)
    (g : Fin S.K) (side : Bool) (x : V) (c : Fin k → ChargeChoices S.K S.M) : Prop :=
  S.bandState g (offsets g) k (fun t ↦ c t g) x = some side ∧
    2 * S.front g (offsets g) k side + S.D < 2 * orientedDepth S.depth side x

/-- The finite temporal-binomial and spatial-label tail at a fixed pair time. -/
noncomputable def badEndpointTail {V : Type*} (S : CollarScan V I) (k μ : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ S.D < 4 * S.r₀ * j),
    ((recentChargeTimes k (4 * S.n * (S.r₀ * j + 1))).card.choose j : ℝ) *
      ((((1 + 2 * (2 * S.r₀) * (2 * S.r₀ + 1)) * μ : ℕ) : ℝ) *
        (1 / (2 * (S.M : ℝ)))) ^ j

open Classical in
/-- A finite binomial tail for an actual bad endpoint in an induced lattice domain.
All charge-path existence, geometry, counting, and selected-coordinate probability
bounds are derived. The sole multiplicity premise counts labels at each anchor.
The time-window cardinality includes its final endpoint. -/
theorem sum_chargePathWeight_bad_endpoint_domainGraph_le
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    {k L μ : ℕ} (offsets : Fin S.K → Fin S.m) (g : Fin S.K) (side : Bool)
    (x : Site Λ) (hxA : x ∈ S.A) (hn : 0 < S.n) (hM : 0 < S.M)
    (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hmult : ∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ μ) :
    (∑ c : Fin k → ChargeChoices S.K S.M,
      if S.IsBadBandEndpoint offsets g side x c
      then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0) ≤
      S.badEndpointTail k μ := by
  classical
  have hcover := S.sum_chargePathWeight_le_sum_of_selected_list_cover hM offsets g side
    (S.badChargePaths x k)
    (fun _ he ↦ S.time_lt_of_mem_badChargePaths he)
    (fun _ he ↦ S.distinct_times_of_mem_badChargePaths he)
    (S.IsBadBandEndpoint offsets g side x) ?_
  · apply hcover.trans
    apply S.sum_badChargePaths_le x k _ _ (by positivity)
    intro y
    rw [hgraph]
    exact card_nearbyChargeLabels_domainGraph_le Λ S.anchor S.r₀ μ hmult y
  · intro c hc
    let choices : ℕ → Bool × Fin S.M := fun t ↦
      if ht : t < k then c ⟨t, ht⟩ g else (false, ⟨0, hM⟩)
    have hchoices : (fun t : Fin k ↦ choices t) = fun t ↦ c t g := by
      funext t
      simp only [choices, dite_eq_left t.isLt]
    have hx : S.bandState g (offsets g) k (fun t ↦ choices t) x = some side := by
      rw [hchoices]
      exact hc.1
    obtain ⟨events, he⟩ := S.bandState_has_chargeAncestry_domainGraph hT hgraph hdepth
      g (offsets g) choices hL hclear k side x hxA hx
    have hvariation : ∀ i y, y ∈ S.ball i →
        |S.depth y - S.depth (S.anchor i)| ≤ S.r₀ :=
      S.abs_depth_sub_anchor_le_domainGraph_of_mem_ball hT hgraph hdepth
    have hmem := he.mem_badChargePaths S hn hvariation hc.2
    refine ⟨events, hmem, ?_⟩
    intro e hevent
    have hsel := he.selected S e hevent
    have ht := he.time_lt S e hevent
    simpa only [choices, dite_eq_left ht] using hsel

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
