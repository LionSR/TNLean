/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadHistoryAsymptotics

/-!
# Inverse-power probability bounds for actual scan histories

At the source's rounded scales, the probability that any physical scan prefix
has a bad lead decays faster than every fixed inverse power. The result uses
the actual evaluator, uniform labelled charge choices, and lattice ancestry.
Only source geometry assumptions remain: compact target size, ambient row
bounds, target clearance from the cut, and bounded labelled anchor multiplicity.
The exponent 200 in Lemma 9.1 is a specialization of the arbitrary exponent.
Quantum transported states and their entropy gains are separate questions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 9.1, `08-scanner.tex`, lines 309–329, at `openai/math@adc7f124`.
-/

open Filter
open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Scan

universe u

open Classical in
/-- Lemma 9.1's bad-history estimate for actual finite physical histories, with
an arbitrary decay exponent. The threshold precedes the domain, target, labels,
and scanner. Both sides and every old-charge prefix are covered by `IsGoodThrough`.
The target and geometric assumptions are those of the source scanner. -/
theorem eventually_bad_history_probability_le
    {ell kappa mu Cr C1 Ct : ℝ} (hell : 0 < ell) (hkappa : 0 < kappa)
    (hkappamu : kappa < mu) (hmu : mu < 1 - ell)
    (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (I : Type u) [Fintype I] [LinearOrder I]
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan (Site Λ) I),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n →
      S.M = ⌈C1 * n * S.D⌉₊ → (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - ell)⌋₊ + 10 * S.r₀ : ℕ) : ℤ) <
          ambientSupDistance t z) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      (∑ h : History S.K S.m S.M (n * S.m),
        if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤ (n : ℝ) ^ (-p) := by
  have hscalar := eventually_badHistory_bound_le_rpow hell hkappa hmu hCr hC1 hCt
    multiplicity p
  filter_upwards [hscalar, eventually_one_le_roundedLogRadius hCr,
    eventually_ge_atTop (1 : ℕ)] with n hscalar hr hn
  intro I _ _ Λ T hT S hSn hm hK hD hR hM ht hgraph hdepth hclear hrows hmult
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hnNat : 0 < S.n := by omega
  have hmNat : 0 < S.m := by
    rw [hm]
    apply lt_of_lt_of_le Nat.zero_lt_one
    apply (Nat.one_le_floor_iff _).mpr
    exact Real.one_le_rpow hnR (by linarith : 0 ≤ mu)
  have hDpos : 0 < S.D := by
    rw [hD]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos _)
  have hMpos : 0 < S.M := by
    rw [hM]
    apply Nat.ceil_pos.mpr
    exact mul_pos (mul_pos hC1 hnpos) (by exact_mod_cast hDpos)
  have hL : 8 * S.K * S.m ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ := by
    rw [hK]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      Nat.div_mul_le_self ⌊(n : ℝ) ^ (1 - ell)⌋₊ (8 * S.m)
  exact (S.sum_historyWeight_bad_through_geometric_domainGraph_le hT hgraph hdepth
    hnNat hmNat (by omega : 0 < S.r₀) hMpos hL hclear hrows hmult).trans
      (hscalar (Site Λ) I S T.card hSn hm hK hD hR hM ht)

end TNLean.PEPS.AreaLaw.Scan
