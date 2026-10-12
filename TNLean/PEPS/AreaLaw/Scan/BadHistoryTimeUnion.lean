/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryUnion
import TNLean.PEPS.AreaLaw.Scan.CompactCollarCounting
import TNLean.PEPS.AreaLaw.Scan.HistoryPrefixes

/-!
# Finite bad-history bound through all scan times

All prefix tests are evaluated on one actual full history. Exact prefix
marginals and a finite union bound give the sum of the already proved
single-time bounds. The compact endpoint factor is bounded by `|T| + nL`
from the actual ambient layer assumption. Neither exterior volume nor a
supplied probability estimate occurs.

This finite estimate precedes the asymptotic choice of logarithmic radius and
power-law charge width; it does not assert the eventual `n⁻²⁰⁰` specialization.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 286–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I]

namespace CollarScan

/-- Every completed pair of one actual full history is good. Scheduled fills
between these states are then good as well. -/
def IsGoodThrough {V : Type*} [Fintype V] [DecidableEq V]
    (S : CollarScan V I) {N : ℕ} (h : History S.K S.m S.M N) : Prop :=
  ∀ t : Fin (N + 1), S.IsGoodCompletedHistory
    (prefixHistory h t (Nat.le_of_lt_succ t.isLt))

/-- Completed-prefix goodness covers every old-charge state at those prefixes. -/
theorem IsGoodThrough.old {V : Type*} [Fintype V] [DecidableEq V]
    (S : CollarScan V I) {N : ℕ} {h : History S.K S.m S.M N}
    (hg : S.IsGoodThrough h) (t : Fin (N + 1)) :
    S.IsGoodOldHistory (prefixHistory h t (Nat.le_of_lt_succ t.isLt)) :=
  S.isGoodOldHistory_of_isGoodCompletedHistory _ (hg t)

open Classical in
/-- Union over all actual prefix times, both sides, all bands, and compact endpoints,
with independent offsets averaged. The only site-count hypotheses are the source
ambient row bound and bounded interaction-label multiplicity. -/
theorem sum_historyWeight_bad_through_domainGraph_le
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x ↦ ambientDepth T hT x.val)
    {N L μ : ℕ} (hn : 0 < S.n) (hm : 0 < S.m) (hM : 0 < S.M)
    (hL : 8 * S.K * S.m ≤ L)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ μ) :
    (∑ h : History S.K S.m S.M N, if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤
      (S.K * 2 * (T.card + S.n * L) : ℕ) *
        ∑ t : Fin (N + 1), S.badEndpointTail t μ := by
  classical
  let C : ℝ := (S.K * 2 * (S.A.filter fun x ↦ S.depth x ≤ L).card : ℕ)
  have htail (t : ℕ) : 0 ≤ S.badEndpointTail t μ := by
    unfold badEndpointTail
    exact Finset.sum_nonneg fun _ _ ↦ by positivity
  have hC : C ≤ (S.K * 2 * (T.card + S.n * L) : ℕ) := by
    dsimp [C]
    apply Nat.cast_le.mpr
    apply Nat.mul_le_mul_left
    simpa only [hdepth] using card_compact_collar_le hT S.A S.n L hrows
  calc
    _ ≤ ∑ h : History S.K S.m S.M N, ∑ t : Fin (N + 1),
        if ¬ S.IsGoodCompletedHistory (prefixHistory h t (Nat.le_of_lt_succ t.isLt))
        then historyWeight h else 0 := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hg : S.IsGoodThrough h
      · simp only [hg, not_true_eq_false, ite_false]
        exact Finset.sum_nonneg fun _ _ ↦ by
          split_ifs <;> first | exact le_rfl | exact historyWeight_nonneg h
      · obtain ⟨t, ht⟩ := not_forall.mp hg
        simpa only [hg, not_false_eq_true, ite_true, ht] using
          (Finset.single_le_sum
            (f := fun t : Fin (N + 1) ↦
              if ¬ S.IsGoodCompletedHistory (prefixHistory h t (Nat.le_of_lt_succ t.isLt))
              then historyWeight h else 0)
            (fun _ _ ↦ by split_ifs <;> first | exact le_rfl | exact historyWeight_nonneg h)
            (Finset.mem_univ t))
    _ = ∑ t : Fin (N + 1), ∑ h : History S.K S.m S.M N,
        if ¬ S.IsGoodCompletedHistory (prefixHistory h t (Nat.le_of_lt_succ t.isLt))
        then historyWeight h else 0 := Finset.sum_comm
    _ = ∑ t : Fin (N + 1), ∑ h : History S.K S.m S.M t,
        if ¬ S.IsGoodCompletedHistory h then historyWeight h else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      simpa only [mul_ite, mul_one, mul_zero] using
        sum_historyWeight_mul_prefix hM (Nat.le_of_lt_succ t.isLt)
          (fun h : History S.K S.m S.M t ↦ if ¬ S.IsGoodCompletedHistory h then 1 else 0)
    _ ≤ ∑ t : Fin (N + 1), C * S.badEndpointTail t μ := by
      apply Finset.sum_le_sum
      intro t _
      exact S.sum_historyWeight_bad_completed_domainGraph_le hT hgraph hdepth
        hn hm hM hL hclear hmult
    _ = C * ∑ t : Fin (N + 1), S.badEndpointTail t μ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun t _ ↦ htail t)

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
