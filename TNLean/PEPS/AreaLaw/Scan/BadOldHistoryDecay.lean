/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalBadHistoryDecay
import TNLean.PEPS.AreaLaw.Scan.StatusScaleSeparation
import TNLean.PEPS.AreaLaw.Geometry.Exponents

/-!
# Uniform old-history tails and the split-counting margin

Each old-history event has its exact full-history marginal. A bad old prefix
forces failure of goodness through the complete history, so its probability
is bounded by the already established all-time tail without a second union
over rounds. At the fixed scanner exponents, one threshold also supplies
the stronger margin 4(D + 2r₀) ≤ m required for counting split labels.

The threshold precedes the physical domain, labelled scanner and round. These
are classical estimates and impose no condition on a replica vector or an
interpolation parameter.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32–58, 309–329 and 492–511, and
`scanner:final-parameters`, at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open Filter
open scoped BigOperators

namespace TNLean.PEPS.AreaLaw.Scan

universe u

namespace CollarScan

open Classical in
/-- A bad old prefix is contained in the failure of all-time goodness on one
full history, with its exact classical marginal and no additional round factor.
Source: `08-scanner.tex`, lines 309–329 and 492–511. -/
theorem sum_historyWeight_bad_old_le_bad_through
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) {s N : ℕ} (hM : 0 < S.M) (hs : s ≤ N) :
    (∑ h : History S.K S.m S.M s,
      if S.IsGoodOldHistory h then 0 else historyWeight h) ≤
      ∑ h : History S.K S.m S.M N,
        if ¬ S.IsGoodThrough h then historyWeight h else 0 := by
  calc
    _ = ∑ h : History S.K S.m S.M N,
        if S.IsGoodOldHistory (prefixHistory h s hs) then 0 else historyWeight h := by
      simpa only [mul_ite, mul_zero, mul_one] using
        (sum_historyWeight_mul_prefix hM hs
          (fun h : History S.K S.m S.M s ↦
            if S.IsGoodOldHistory h then (0 : ℝ) else 1)).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hg : S.IsGoodThrough h
      · have hold : S.IsGoodOldHistory (prefixHistory h s hs) :=
          IsGoodThrough.old S hg ⟨s, Nat.lt_succ_of_le hs⟩
        simp only [hold, hg, not_true_eq_false, ite_true, ite_false, le_refl]
      · simp only [hg, not_false_eq_true, ite_true]
        split_ifs
        · exact historyWeight_nonneg h
        · exact le_rfl

end CollarScan

/-- At fixed positive exponent gap, the literal rounded scales satisfy the
stronger split-counting margin, as well as the existing status inequalities.
Source: `08-scanner.tex`, lines 32–58 and 492–511. -/
theorem eventually_split_counting_scale_separation {Cr ell kappa mu : ℝ}
    (hCr : 0 ≤ Cr) (hkappa : 0 < kappa) (hkm : kappa < mu) :
    ∀ᶠ n : ℕ in atTop,
      let L := ⌊(n : ℝ) ^ (1 - ell)⌋₊
      let m := ⌊(n : ℝ) ^ mu⌋₊
      let D := ⌈(n : ℝ) ^ kappa⌉₊
      let K := L / (8 * m)
      2 ≤ n ∧ roundedLogRadius Cr n ≤ D ∧ 1 ≤ D ∧
        4 * (D + 2 * roundedLogRadius Cr n) ≤ m ∧ 8 * K * m ≤ L := by
  have hratio : ∀ᶠ n : ℕ in atTop, (24 : ℝ) ≤ (n : ℝ) ^ (mu - kappa) :=
    ((tendsto_rpow_atTop (sub_pos.mpr hkm)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 24
  filter_upwards [eventually_status_scale_separation (ell := ell) hCr hkappa hkm,
    hratio] with n hstatus hratio
  dsimp only at hstatus ⊢
  obtain ⟨hn, hr, hD, _, hL⟩ := hstatus
  have hmargin : 12 * ⌈(n : ℝ) ^ kappa⌉₊ ≤ ⌊(n : ℝ) ^ mu⌋₊ :=
    mul_ceil_rpow_le_floor_rpow (by omega) hkappa.le (by push_cast; linarith)
  exact ⟨hn, hr, hD, by omega, hL⟩

open Classical in
/-- One threshold at the final scanner exponents controls every classical old
history and supplies the split-counting margin. It is chosen before every
physical instance and every round, hence before replica or parameter choices.
Source: `08-scanner.tex`, lines 309–329, 492–511 and `scanner:final-parameters`. -/
theorem exists_badOldHistory_threshold {Cr C1 Ct : ℝ}
    (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (P : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (I : Type u) [Fintype I] [LinearOrder I]
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan (Site Λ) I),
      S.n = n → S.m = ⌊(n : ℝ) ^ (Exponents.scannerMu : ℝ)⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ (Exponents.scannerKappa : ℝ)⌉₊ →
      S.r₀ = roundedLogRadius Cr n → S.C₁ = C1 →
      (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ +
          10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      2 ≤ S.n ∧ S.r₀ ≤ S.D ∧ 1 ≤ S.D ∧
        4 * (S.D + 2 * S.r₀) ≤ S.m ∧
        8 * S.K * S.m ≤ ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ ∧
        ∀ s : ℕ, s ≤ S.n * S.m →
          (∑ h : History S.K S.m S.M s,
            if S.IsGoodOldHistory h then 0 else historyWeight h) ≤ (n : ℝ) ^ (-P) := by
  have hell : (0 : ℝ) < (Exponents.scannerEll : ℝ) := by
    norm_num [Exponents.scannerEll]
  have hkappa : (0 : ℝ) < (Exponents.scannerKappa : ℝ) := by
    norm_num [Exponents.scannerKappa]
  have hkm : (Exponents.scannerKappa : ℝ) < (Exponents.scannerMu : ℝ) := by
    norm_num [Exponents.scannerKappa, Exponents.scannerMu]
  have hmu : (Exponents.scannerMu : ℝ) < 1 - (Exponents.scannerEll : ℝ) := by
    norm_num [Exponents.scannerMu, Exponents.scannerEll]
  have htail := eventually_bad_history_probability_le hell hkappa hkm hmu
    hCr hC1 hCt multiplicity P
  have hscales := eventually_split_counting_scale_separation
    (ell := (Exponents.scannerEll : ℝ)) hCr.le hkappa hkm
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htail.and hscales)
  refine ⟨N, ?_⟩
  intro n hn I _ _ Λ T hT S hSn hm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  obtain ⟨htail, hscales⟩ := hN n hn
  have hM : S.M = ⌈C1 * n * S.D⌉₊ := by
    simp only [CollarScan.M, chargeSlotCount, hC, hSn]
  have hfull := htail I Λ T hT S hSn hm hK hD hr hM ht hgraph hdepth hclear hrows hmult
  have hscales' : 2 ≤ S.n ∧ S.r₀ ≤ S.D ∧ 1 ≤ S.D ∧
      4 * (S.D + 2 * S.r₀) ≤ S.m ∧
      8 * S.K * S.m ≤ ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ := by
    simpa only [hSn, hm, hK, hD, hr] using hscales
  refine ⟨hscales'.1, hscales'.2.1, hscales'.2.2.1, hscales'.2.2.2.1,
    hscales'.2.2.2.2, ?_⟩
  intro s hs
  have hMpos : 0 < S.M :=
    chargeSlotCount_pos (by simpa only [hC] using hC1) (by omega) hscales'.2.2.1
  exact (S.sum_historyWeight_bad_old_le_bad_through hMpos
    (show s ≤ n * S.m by simpa only [hSn] using hs)).trans hfull

end TNLean.PEPS.AreaLaw.Scan
