/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.AncestryGeometry
import TNLean.PEPS.AreaLaw.Scan.AncestryLead
import TNLean.PEPS.AreaLaw.Scan.ChargePathCounting
import TNLean.PEPS.AreaLaw.Scan.TimedChargePaths

/-!
# Finite charge-path cover of bad endpoints

Actual bad endpoints give long chronologically ordered paths, contained in a
short terminal time window and in the spatial anchor-path family. The cover
below enumerates those paths by length. Its temporal count is binomial; its
spatial count retains the multiplicity of labels at a common anchor.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 286–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

namespace CollarScan

variable (S : CollarScan V I)

/-- The reversed labels of an actual ancestry belong to the finite spatial
anchor-path family. This discards predecessor witnesses without losing labels. -/
theorem ChargeAncestry.labels_mem_chargeAnchorPaths {g r k : ℕ}
    {choices : ℕ → Bool × Fin S.M} {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) :
    (events.map Prod.snd).reverse ∈ chargeAnchorPaths S.graph S.anchor S.r₀ x events.length := by
  rw [mem_chargeAnchorPaths_iff]
  refine ⟨by simp, List.isChain_cons.mpr ⟨?_, ?_⟩⟩
  · intro y hy
    simp only [List.map_reverse, List.map_map, List.head?_reverse, List.getLast?_map,
      Option.mem_def] at hy
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hy
    have hx := h.endpoint_mem_last_ball S e he
    have hb : S.graph.edist (S.anchor e.2) x ≤ (S.r₀ : ℕ∞) :=
      (Finset.mem_filter.mp hx).2
    calc
      S.graph.edist x (S.anchor e.2) = S.graph.edist (S.anchor e.2) x :=
        SimpleGraph.edist_comm
      _ ≤ (S.r₀ : ℕ∞) := hb
      _ ≤ ((2 * S.r₀ : ℕ) : ℕ∞) := by exact_mod_cast (by omega : S.r₀ ≤ 2 * S.r₀)
  · rw [List.map_reverse, List.map_map, List.isChain_reverse, List.isChain_map]
    simpa only [Function.comp_apply, SimpleGraph.edist_comm] using h.anchor_chain S

/-- Strict chronology bounds an ancestry length by the number of completed pairs. -/
theorem ChargeAncestry.length_le {g r k : ℕ} {choices : ℕ → Bool × Fin S.M}
    {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) : events.length ≤ k := by
  have hp : (events.map Prod.fst).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using h.ordered S
  have hn : (events.map Prod.fst).Nodup := hp.imp fun he ↦ ne_of_lt he
  have hsub : (events.map Prod.fst).toFinset ⊆ Finset.range k := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    exact Finset.mem_range.mpr (h.time_lt S e he)
  have hc := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hn, List.length_map, Finset.card_range] using hc

/-- All timed label paths of one possible bad-ancestry length. -/
noncomputable def badChargePathsOfLength (x : V) (k j : ℕ) : Finset (List (ℕ × I)) :=
  timedChargePaths (recentChargeTimes k (4 * S.n * (S.r₀ * j + 1)))
    (chargeAnchorPaths S.graph S.anchor S.r₀ x j) j

/-- Finite cover retaining exactly the lengths allowed by the deterministic bad-lead bound. -/
noncomputable def badChargePaths (x : V) (k : ℕ) : Finset (List (ℕ × I)) :=
  ((Finset.range (k + 1)).filter fun j ↦ S.D < 4 * S.r₀ * j).biUnion
    (S.badChargePathsOfLength x k)

/-- An actual bad ancestry belongs to the explicit finite timed/spatial cover. -/
theorem ChargeAncestry.mem_badChargePaths {g r k : ℕ} {choices : ℕ → Bool × Fin S.M}
    {side : Bool} {x : V} {events : List (ℕ × I)}
    (h : S.ChargeAncestry g r choices side k x events) (hn : 0 < S.n)
    (hdepth : ∀ i y, y ∈ S.ball i → |S.depth y - S.depth (S.anchor i)| ≤ S.r₀)
    (hbad : 2 * S.front g r k side + S.D < 2 * orientedDepth S.depth side x) :
    events ∈ S.badChargePaths x k := by
  obtain ⟨_, hlen, hwindow⟩ := h.bad_length_and_time S hn hdepth hbad
  apply Finset.mem_biUnion.mpr
  refine ⟨events.length, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (Nat.lt_succ_of_le (h.length_le S)), ?_⟩, ?_⟩
  · exact_mod_cast hlen
  · apply mem_timedChargePaths _ _ events (h.ordered S) _ (h.labels_mem_chargeAnchorPaths S)
    intro e he
    apply mem_recentChargeTimes (h.time_lt S e he)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hwindow e he

omit [Fintype V] [DecidableEq V] in
/-- Every enumerated path has its advertised length. -/
theorem length_of_mem_badChargePathsOfLength {x : V} {k j : ℕ} {events : List (ℕ × I)}
    (he : events ∈ S.badChargePathsOfLength x k j) : events.length = j :=
  length_of_mem_timedChargePaths
    (fun _ls hl ↦ (mem_chargeAnchorPaths_iff _ _ _ _ _ _).mp hl |>.1) he

omit [Fintype V] [DecidableEq V] in
/-- Every time in the finite cover is a valid coordinate of the tested history. -/
theorem time_lt_of_mem_badChargePaths {x : V} {k : ℕ} {events : List (ℕ × I)}
    (he : events ∈ S.badChargePaths x k) : ∀ e ∈ events, e.1 < k := by
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp he
  intro e hevent
  have hw := time_mem_of_mem_timedChargePaths hj e hevent
  exact (Finset.mem_Ico.mp hw).2

omit [Fintype V] [DecidableEq V] in
/-- The finite cover has distinct charge times, including when labels repeat. -/
theorem distinct_times_of_mem_badChargePaths {x : V} {k : ℕ} {events : List (ℕ × I)}
    (he : events ∈ S.badChargePaths x k) : (events.map Prod.fst).Nodup := by
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp he
  have ho := ordered_of_mem_timedChargePaths
    (fun _ls hl ↦ (mem_chargeAnchorPaths_iff _ _ _ _ _ _).mp hl |>.1) hj
  have hp : (events.map Prod.fst).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using ho
  exact hp.imp fun h ↦ ne_of_lt h

omit [Fintype V] [DecidableEq V] in
/-- The spatial family supplies the power factor; times contribute the binomial coefficient. -/
theorem card_badChargePathsOfLength_le (x : V) (k j B : ℕ)
    (hlabels : ∀ y, (nearbyChargeLabels S.graph S.anchor S.r₀ y).card ≤ B) :
    (S.badChargePathsOfLength x k j).card ≤
      (recentChargeTimes k (4 * S.n * (S.r₀ * j + 1))).card.choose j * B ^ j := by
  exact (card_timedChargePaths_le _ _ _).trans
    (Nat.mul_le_mul_left _ (card_chargeAnchorPaths_le _ _ _ _ hlabels x j))

omit [Fintype V] [DecidableEq V] in
/-- The full finite weighted cover has a binomial temporal factor and a spatial
power factor. Distinct lengths are disjoint, so this sum introduces no hidden
multiplicity beyond the already counted labelled paths. -/
theorem sum_badChargePaths_le (x : V) (k B : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hlabels : ∀ y, (nearbyChargeLabels S.graph S.anchor S.r₀ y).card ≤ B) :
    (∑ events ∈ S.badChargePaths x k, q ^ events.length) ≤
      ∑ j ∈ (Finset.range (k + 1)).filter (fun j ↦ S.D < 4 * S.r₀ * j),
        ((recentChargeTimes k (4 * S.n * (S.r₀ * j + 1))).card.choose j : ℝ) *
          ((B : ℝ) * q) ^ j := by
  classical
  unfold badChargePaths
  rw [Finset.sum_biUnion]
  · apply Finset.sum_le_sum
    intro j _
    calc
      (∑ events ∈ S.badChargePathsOfLength x k j, q ^ events.length) =
          (S.badChargePathsOfLength x k j).card * q ^ j := by
        rw [Finset.sum_congr rfl (fun e he ↦ congrArg (q ^ ·)
          (S.length_of_mem_badChargePathsOfLength he))]
        simp
      _ ≤ ((recentChargeTimes k (4 * S.n * (S.r₀ * j + 1))).card.choose j * B ^ j : ℕ) *
          q ^ j := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq _)
        exact_mod_cast S.card_badChargePathsOfLength_le x k j B hlabels
      _ = _ := by push_cast; rw [mul_pow]; ring
  · intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro events hea heb
    exact hab ((S.length_of_mem_badChargePathsOfLength hea).symm.trans
      (S.length_of_mem_badChargePathsOfLength heb))

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
