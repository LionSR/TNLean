/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryProbability

/-!
# Compact-endpoint union and offset averaging for bad histories

A bad old-charge history was already bad before its preceding fill. Its bad
endpoint lies in the compact initial collar. Union over both sides, all bands,
and those collar sites, then average the independent uniform initial offsets.
No factor involving the physical exterior volume appears.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 286–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

namespace CollarScan

/-- Goodness at a completed fill/charge pair, using the actual assigned sites
of the chosen color and the deterministic front after those pairs. -/
def IsGoodCompletedHistory {V : Type*} [Fintype V] [DecidableEq V]
    (S : CollarScan V I) {k : ℕ} (h : History S.K S.m S.M k) : Prop :=
  ∀ (g : Fin S.K) (side : Bool) (x : V), x ∈ S.A → S.state h g x = some side →
    2 * orientedDepth S.depth side x ≤ 2 * S.front g (h.1 g) k side + S.D

/-- A deterministic fill cannot destroy goodness, including when its slot is
blank or previously assigned. Hence completed-state tests cover old charge states. -/
theorem isGoodOldHistory_of_isGoodCompletedHistory {V : Type*} [Fintype V] [DecidableEq V]
    (S : CollarScan V I) {k : ℕ} (h : History S.K S.m S.M k)
    (hg : S.IsGoodCompletedHistory h) : S.IsGoodOldHistory h := by
  intro g side x hxA hx
  by_contra hbad
  have hb := S.oldChargeState_bad_implies_state_bad h g side x hx (lt_of_not_ge hbad)
  exact (not_lt_of_ge (hg g side x hxA hb.1)) hb.2

open Classical in
/-- Conditional on all offsets, the completed-history bad event has a finite bound
with only compact collar volume, two sides, and the number of bands. -/
theorem sum_chargePathWeight_bad_completed_domainGraph_le
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    {k L μ : ℕ} (offsets : Fin S.K → Fin S.m) (hn : 0 < S.n) (hM : 0 < S.M)
    (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hmult : ∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ μ) :
    (∑ c : Fin k → ChargeChoices S.K S.M,
      if ¬ S.IsGoodCompletedHistory (offsets, c)
      then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0) ≤
      (S.K * 2 * (S.A.filter fun x ↦ S.depth x ≤ L).card : ℕ) * S.badEndpointTail k μ := by
  classical
  let points := S.A.filter fun x ↦ S.depth x ≤ L
  let tests : Finset (Fin S.K × Bool × Site Λ) := Finset.univ ×ˢ (Finset.univ ×ˢ points)
  let w : ℝ := ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k
  let E (a : Fin S.K × Bool × Site Λ) (c : Fin k → ChargeChoices S.K S.M) :=
    S.IsBadBandEndpoint offsets a.1 a.2.1 a.2.2 c
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hcover (c : Fin k → ChargeChoices S.K S.M)
      (hc : ¬ S.IsGoodCompletedHistory (offsets, c)) : ∃ a ∈ tests, E a c := by
    simp only [IsGoodCompletedHistory, not_forall] at hc
    obtain ⟨g, side, x, hx⟩ := hc
    push Not at hx
    obtain ⟨hxA, hs, hbad⟩ := hx
    have hb : S.IsBadBandEndpoint offsets g side x c := ⟨hs, hbad⟩
    have hcompact := S.bad_bandState_mem_collar g (offsets g) hL
      (fun t ↦ c t g) side x hxA hb.1 hb.2
    refine ⟨(g, side, x), ?_, hb⟩
    simp only [tests, points, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_filter]
    exact hcompact
  calc
    _ ≤ ∑ c : Fin k → ChargeChoices S.K S.M,
        ∑ a ∈ tests, if E a c then w else 0 := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : ¬ S.IsGoodCompletedHistory (offsets, c)
      · obtain ⟨a, ha, he⟩ := hcover c hc
        simpa only [hc, not_false_eq_true, ite_true, he, w] using
          (Finset.single_le_sum (f := fun a ↦ if E a c then w else 0)
            (fun _ _ ↦ by split_ifs <;> positivity) ha)
      · simp only [hc, ite_false]
        exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity
    _ = ∑ a ∈ tests, ∑ c : Fin k → ChargeChoices S.K S.M,
        if E a c then w else 0 := Finset.sum_comm
    _ ≤ ∑ _a ∈ tests, S.badEndpointTail k μ := by
      apply Finset.sum_le_sum
      intro a ha
      have hxA : a.2.2 ∈ S.A :=
        (Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_product.mp ha).2).2).1
      exact S.sum_chargePathWeight_bad_endpoint_domainGraph_le hT hgraph hdepth offsets
        a.1 a.2.1 a.2.2 hxA hn hM hL hclear hmult
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, tests, points, Finset.card_product,
        Finset.card_univ, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul]
      ring

open Classical in
/-- Averaging the actual independent initial offsets preserves the finite bad-history bound.
The weights are the scanner's classical history weights, not transported quantum measures. -/
theorem sum_historyWeight_bad_completed_domainGraph_le
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    {k L μ : ℕ} (hn : 0 < S.n) (hm : 0 < S.m) (hM : 0 < S.M)
    (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hmult : ∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ μ) :
    (∑ h : History S.K S.m S.M k, if ¬ S.IsGoodCompletedHistory h then historyWeight h else 0) ≤
      (S.K * 2 * (S.A.filter fun x ↦ S.depth x ≤ L).card : ℕ) * S.badEndpointTail k μ := by
  classical
  let B : ℝ := (S.K * 2 * (S.A.filter fun x ↦ S.depth x ≤ L).card : ℕ) * S.badEndpointTail k μ
  have hm0 : (S.m : ℝ) ≠ 0 := by positivity
  calc
    _ = ∑ offsets : Fin S.K → Fin S.m, (1 / (S.m : ℝ)) ^ S.K *
        ∑ c : Fin k → ChargeChoices S.K S.M,
          if ¬ S.IsGoodCompletedHistory (offsets, c)
          then ((1 / (2 * (S.M : ℝ))) ^ S.K) ^ k else 0 := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.mul_sum, mul_ite, mul_zero, historyWeight]
    _ ≤ ∑ _offsets : Fin S.K → Fin S.m, (1 / (S.m : ℝ)) ^ S.K * B := by
      apply Finset.sum_le_sum
      intro offsets _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact S.sum_chargePathWeight_bad_completed_domainGraph_le hT hgraph hdepth offsets
        hn hM hL hclear hmult
    _ = B := by simp [Nat.cast_pow, hm0]

open Classical in
/-- The same finite bound applies to old charge histories, because fills cannot
create bad lead. This covers the source's sampling-time goodness convention. -/
theorem sum_historyWeight_bad_old_domainGraph_le
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    {k L μ : ℕ} (hn : 0 < S.n) (hm : 0 < S.m) (hM : 0 < S.M)
    (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hmult : ∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ μ) :
    (∑ h : History S.K S.m S.M k, if ¬ S.IsGoodOldHistory h then historyWeight h else 0) ≤
      (S.K * 2 * (S.A.filter fun x ↦ S.depth x ≤ L).card : ℕ) * S.badEndpointTail k μ := by
  classical
  apply le_trans _ (S.sum_historyWeight_bad_completed_domainGraph_le hT hgraph hdepth
    hn hm hM hL hclear hmult)
  apply Finset.sum_le_sum
  intro h _
  by_cases hc : S.IsGoodCompletedHistory h
  · have ho := S.isGoodOldHistory_of_isGoodCompletedHistory h hc
    simp only [hc, ho, not_true_eq_false, ite_false, le_refl]
  · simp only [hc, not_false_eq_true, ite_true]
    by_cases ho : S.IsGoodOldHistory h
    · simp only [ho, not_true_eq_false, ite_false]
      exact historyWeight_nonneg h
    · simp only [ho, not_false_eq_true, ite_true, le_refl]

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
