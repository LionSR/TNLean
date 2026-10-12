/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryTimeUnion
import TNLean.PEPS.AreaLaw.Scan.ChargeBinomialBound

/-!
# A geometric finite tail for actual bad scan histories

The binomial factorial cancels the ancestry length in the time-window bound.
Counting labelled anchor paths alone gives a ratio proportional to
`nr₀ (1+r₀²) μ / M`, sharper than counting predecessor sites as well. This
ratio follows from actual extracted paths and actual lattice diamond volume.
The result is finite and precedes the asymptotic scale specialization.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 309–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

namespace CollarScan

variable {V I : Type*}

/-- Length-independent ratio obtained after the temporal factorial cancellation. -/
noncomputable def badChargeRatio (S : CollarScan V I) (μ : ℕ) : ℝ :=
  Real.exp 1 * (9 * (S.n : ℝ) * S.r₀) *
    ((((1 + 2 * (2 * S.r₀) * (2 * S.r₀ + 1)) * μ : ℕ) : ℝ) /
      (2 * (S.M : ℝ)))

/-- Finite geometric sum over lengths that can produce a bad lead. -/
noncomputable def geometricBadTail (S : CollarScan V I) (N μ : ℕ) : ℝ :=
  ∑ j ∈ (Finset.range (N + 1)).filter (fun j ↦ S.D < 4 * S.r₀ * j),
    S.badChargeRatio μ ^ j

/-- The exact temporal-binomial tail is bounded by one geometric ratio.
Strict positivity of the radius is only needed for this simplified window estimate. -/
theorem badEndpointTail_le_geometricBadTail (S : CollarScan V I) (k μ : ℕ)
    (hn : 0 < S.n) (hr : 0 < S.r₀) :
    S.badEndpointTail k μ ≤ S.geometricBadTail k μ := by
  unfold badEndpointTail geometricBadTail
  apply Finset.sum_le_sum
  intro j hj
  have hjpos : 0 < j := by
    have hh := (Finset.mem_filter.mp hj).2
    by_contra hz
    have hj0 : j = 0 := by omega
    simp only [hj0, mul_zero, Nat.not_lt_zero] at hh
  have hw := card_ancestry_time_window_le hn hr hjpos k
  have hwR : ((recentChargeTimes k (4 * S.n * (S.r₀ * j + 1))).card : ℝ) ≤
      (9 * (S.n : ℝ) * S.r₀) * j := by exact_mod_cast hw
  simpa only [badChargeRatio, div_eq_mul_inv, one_mul] using
    choose_mul_pow_le_of_window_bound
      (recentChargeTimes k (4 * S.n * (S.r₀ * j + 1))).card j hjpos
      ((((1 + 2 * (2 * S.r₀) * (2 * S.r₀ + 1)) * μ : ℕ) : ℝ) *
        (1 / (2 * (S.M : ℝ)))) (9 * (S.n : ℝ) * S.r₀) (by positivity) hwR

/-- Increasing the observation horizon only adds nonnegative length terms. -/
theorem geometricBadTail_mono (S : CollarScan V I) (μ : ℕ) :
    Monotone (fun N ↦ S.geometricBadTail N μ) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.filter_subset_filter
    exact Finset.range_mono (Nat.add_le_add_right hab 1)
  · intro _ _ _
    unfold badChargeRatio
    positivity

open Classical in
/-- One explicit finite geometric bound controls every actual scan time, both
sides and all bands, averaged over offsets. Its endpoint factor is compact and
its ratio is derived, not supplied as a probability hypothesis. -/
theorem sum_historyWeight_bad_through_geometric_domainGraph_le
    [Fintype I] [LinearOrder I] {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    {N L μ : ℕ} (hn : 0 < S.n) (hm : 0 < S.m) (hr : 0 < S.r₀) (hM : 0 < S.M)
    (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ μ) :
    (∑ h : History S.K S.m S.M N, if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤
      (S.K * 2 * (T.card + S.n * L) * (N + 1) : ℕ) * S.geometricBadTail N μ := by
  apply le_trans (S.sum_historyWeight_bad_through_domainGraph_le hT hgraph hdepth
    hn hm hM hL hclear hrows hmult)
  calc
    _ ≤ (S.K * 2 * (T.card + S.n * L) : ℕ) *
        ∑ _t : Fin (N + 1), S.geometricBadTail N μ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro t _
      exact (S.badEndpointTail_le_geometricBadTail t μ hn hr).trans
        (S.geometricBadTail_mono μ (Nat.le_of_lt_succ t.isLt))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul]; ring

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
