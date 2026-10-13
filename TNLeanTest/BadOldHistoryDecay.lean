/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.BadOldHistoryDecay

/-! # Exact old-history marginals and uniform fixed-exponent thresholds -/

set_option autoImplicit false

open Filter
open scoped BigOperators
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

namespace TNLeanTest.BadOldHistoryDecay

universe u

open Classical in
/-- The threshold precedes the actual scanner, its labels and every old round. -/
theorem fixed_exponent_signature {Cr C1 Ct : ℝ}
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
            if S.IsGoodOldHistory h then 0 else historyWeight h) ≤ (n : ℝ) ^ (-P) :=
  exists_badOldHistory_threshold hCr hC1 hCt multiplicity P

open Classical in
/-- The empty charge prefix has the exact marginal, with no positivity of m. -/
theorem initial_prefix
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (N : ℕ) (hM : 0 < S.M) :
    (∑ h : History S.K S.m S.M 0,
      if S.IsGoodOldHistory h then 0 else historyWeight h) ≤
      ∑ h : History S.K S.m S.M N,
        if ¬ S.IsGoodThrough h then historyWeight h else 0 :=
  S.sum_historyWeight_bad_old_le_bad_through hM (Nat.zero_le N)

open Classical in
/-- The inclusive final prefix is also covered, though actual next charges
use the stricter horizon s + 1 ≤ nm. -/
theorem final_prefix
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (N : ℕ) (hM : 0 < S.M) :
    (∑ h : History S.K S.m S.M N,
      if S.IsGoodOldHistory h then 0 else historyWeight h) ≤
      ∑ h : History S.K S.m S.M N,
        if ¬ S.IsGoodThrough h then historyWeight h else 0 :=
  S.sum_historyWeight_bad_old_le_bad_through hM le_rfl

open Classical in
/-- Zero bands give zero bad-old mass even without nonempty slots or offsets. -/
theorem zero_band_bad_old
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hK : S.K = 0) (s : ℕ) :
    (∑ h : History S.K S.m S.M s,
      if S.IsGoodOldHistory h then 0 else historyWeight h) = 0 := by
  have hgood (h : History S.K S.m S.M s) : S.IsGoodOldHistory h := by
    intro g
    have hg := g.isLt
    omega
  simp only [hgood, ite_true, Finset.sum_const_zero]

/-- The stronger margin is automatic at the actual fixed rational exponents. -/
theorem fixed_exponent_margin {Cr : ℝ} (hCr : 0 ≤ Cr) :
    ∀ᶠ n : ℕ in atTop,
      let L := ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
      let m := ⌊(n : ℝ) ^ (Exponents.scannerMu : ℝ)⌋₊
      let D := ⌈(n : ℝ) ^ (Exponents.scannerKappa : ℝ)⌉₊
      let K := L / (8 * m)
      2 ≤ n ∧ roundedLogRadius Cr n ≤ D ∧ 1 ≤ D ∧
        4 * (D + 2 * roundedLogRadius Cr n) ≤ m ∧ 8 * K * m ≤ L :=
  eventually_split_counting_scale_separation hCr
    (by norm_num [Exponents.scannerKappa])
    (by norm_num [Exponents.scannerKappa, Exponents.scannerMu])

end TNLeanTest.BadOldHistoryDecay
