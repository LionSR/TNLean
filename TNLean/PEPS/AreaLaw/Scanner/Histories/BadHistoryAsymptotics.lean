/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scanner.Histories.BadHistoryPowerBound
import TNLean.PEPS.AreaLaw.Collar.Scales.RadiusAsymptotics
import TNLean.PEPS.AreaLaw.Scanner.Histories.BadHistoryGeometricTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Arbitrary inverse-power decay of the actual finite bad-history bound

The radius is the rounded squared logarithm, the lookahead and window are
rounded powers, and the charge capacity is the source ceiling. Every constant
and every asymptotic threshold is chosen before the finite lattice, target,
label family, and actual scanner. No eventual scale comparison or probability
estimate is an input. The threshold is given explicitly by `badHistoryThreshold`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 9.1, `08-scanner.tex`, lines 309–329, at `openai/math@adc7f124`.

It also contains the following results.

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.badChargeRatio_le_radius_cube`,
  `TNLean.PEPS.AreaLaw.Scan.CollarScan.source_lengths_le`: the actual charge ratio at the rounded
  source capacity.
* `TNLean.PEPS.AreaLaw.Scan.bad_history_probability_le_of_threshold_le`,
  `TNLean.PEPS.AreaLaw.Scan.eventually_bad_history_probability_le`: inverse-power probability bounds
  for actual scan histories.
-/

section BadChargeRatioBound

/-!
## The actual charge ratio at the rounded source capacity

The two-dimensional diamond count is at most thirteen times the squared
radius. The padded capacity is the ceiling of the source expression, so its
rounding only improves the bad-history estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 309–329, at `openai/math@adc7f124`.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

variable {V I : Type*}

/-- Cancellation of the physical row size in the actual charge ratio. -/
theorem badChargeRatio_le_radius_cube (S : CollarScan V I) (multiplicity : ℕ)
    {C1 : ℝ} (hC1 : 0 < C1) (hn : 0 < S.n) (hD : 0 < S.D)
    (hr : 1 ≤ S.r₀) (hM : C1 * S.n * S.D ≤ S.M) :
    S.badChargeRatio multiplicity ≤
      (117 * Real.exp 1 * multiplicity / (2 * C1)) * (S.r₀ : ℝ) ^ 3 / S.D := by
  have hnR : (0 : ℝ) < S.n := by exact_mod_cast hn
  have hDR : (0 : ℝ) < S.D := by exact_mod_cast hD
  have hrR : (1 : ℝ) ≤ S.r₀ := by exact_mod_cast hr
  have hMR : (0 : ℝ) < S.M := lt_of_lt_of_le (by positivity) hM
  have hball : (1 + 2 * (2 * S.r₀) * (2 * S.r₀ + 1) : ℝ) ≤
      13 * (S.r₀ : ℝ) ^ 2 := by nlinarith
  unfold badChargeRatio
  push_cast
  calc
    _ ≤ Real.exp 1 * (9 * (S.n : ℝ) * S.r₀) *
        ((13 * (S.r₀ : ℝ) ^ 2 * multiplicity) / (2 * (C1 * S.n * S.D))) := by
      gcongr
    _ = _ := by field_simp; ring

/-- Floors do not increase either source length beyond the ambient scale. -/
theorem source_lengths_le {n : ℕ} {ell mu : ℝ} (hn : 1 ≤ n)
    (hell : 0 ≤ ell) (hmu : mu ≤ 1) :
    ⌊(n : ℝ) ^ (1 - ell)⌋₊ ≤ n ∧ ⌊(n : ℝ) ^ mu⌋₊ ≤ n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · exact_mod_cast (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
      ((Real.rpow_le_rpow_of_exponent_le hnR (by linarith : 1 - ell ≤ 1)).trans_eq
        (Real.rpow_one _))
  · exact_mod_cast (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
      ((Real.rpow_le_rpow_of_exponent_le hnR hmu).trans_eq (Real.rpow_one _))

end TNLean.PEPS.AreaLaw.Scan.CollarScan

end BadChargeRatioBound

section BadHistoryAsymptotics

open Filter

namespace TNLean.PEPS.AreaLaw.Scan

universe u v

/-- The number `J = ⌈(p + 8) / (κ / 2)⌉₊` of charge-ratio factors in the geometric bad tail
that gives decay `n^{-p}` after the polynomial prefactor `n^8` (Lemma 9.1,
`08-scanner.tex`, lines 309–329). -/
noncomputable def badHistoryTailCount (kappa p : ℝ) : ℕ :=
  ⌈(p + 8) / (kappa / 2)⌉₊

/-- The explicit threshold of the bad-history bound of Lemma 9.1: the rounded-radius
thresholds for `117 e μ / (2 C₁) r₀³ ≤ n^{κ/2}` and `4 J r₀ ≤ n^κ`, and `n ≥ 8 (C_t + 1)`
(`08-scanner.tex`, lines 309–329). -/
noncomputable def badHistoryThreshold (kappa Cr C1 Ct : ℝ) (multiplicity : ℕ) (p : ℝ) : ℕ :=
  max (roundedLogRadiusThreshold Cr (kappa / 2) (117 * Real.exp 1 * multiplicity / (2 * C1)) 3)
    (max (roundedLogRadiusThreshold Cr kappa (4 * badHistoryTailCount kappa p) 1)
      ⌈8 * (Ct + 1)⌉₊)

/-- The bad-history threshold is at least `3`. -/
theorem three_le_badHistoryThreshold (kappa Cr C1 Ct : ℝ) (multiplicity : ℕ) (p : ℝ) :
    3 ≤ badHistoryThreshold kappa Cr C1 Ct multiplicity p :=
  le_trans (by simp [roundedLogRadiusThreshold]) (le_max_left _ _)

/-- The finite expression proved from actual ancestry is at most `n^{-p}` at every `n` from
the explicit threshold `badHistoryThreshold kappa Cr C1 Ct multiplicity p` on, uniformly in
the scanner and target (Lemma 9.1, `08-scanner.tex`, lines 309–329). -/
theorem badHistory_bound_le_rpow_of_threshold_le
    {ell kappa mu Cr C1 Ct : ℝ} (hell : 0 < ell) (hkappa : 0 < kappa)
    (hmu : mu < 1 - ell) (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (p : ℝ) {n : ℕ}
    (hthr : badHistoryThreshold kappa Cr C1 Ct multiplicity p ≤ n) :
    ∀ (V : Type u) (I : Type v) (S : CollarScan V I) (t : ℕ),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n →
      S.M = ⌈C1 * n * S.D⌉₊ → (t : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      ((S.K * 2 * (t + S.n * ⌊(n : ℝ) ^ (1 - ell)⌋₊) *
        (n * S.m + 1) : ℕ) : ℝ) * S.geometricBadTail (n * S.m) multiplicity ≤
        (n : ℝ) ^ (-p) := by
  set J := badHistoryTailCount kappa p
  have hJ : (p + 8) / (kappa / 2) ≤ (J : ℝ) := Nat.le_ceil _
  have hJ' : p + 8 ≤ kappa / 2 * (J : ℝ) := by
    have := (div_le_iff₀ (by positivity : 0 < kappa / 2)).mp hJ
    linarith
  have hn3 : 3 ≤ n := (three_le_badHistoryThreshold _ _ _ _ _ _).trans hthr
  simp only [badHistoryThreshold, max_le_iff] at hthr
  obtain ⟨hcube, hcut, hc⟩ := hthr
  have hcube := const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le hCr.le
    (show 0 < kappa / 2 by positivity) _ 3 hcube
  have hcut := const_mul_roundedLogRadius_pow_le_rpow_of_threshold_le hCr.le hkappa _ 1 hcut
  rw [pow_one] at hcut
  have hc : 8 * (Ct + 1) ≤ (n : ℝ) := Nat.ceil_le.mp hc
  have hr := one_le_roundedLogRadius_of_two_le hCr (show 2 ≤ n by omega)
  have hn : 1 ≤ n := by omega
  intro V I S t hSn hm hK hD hR hM ht
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hnNat : 0 < S.n := by omega
  have hDpos : 0 < S.D := by
    rw [hD]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos _)
  have hDR : (n : ℝ) ^ kappa ≤ S.D := by rw [hD]; exact Nat.le_ceil _
  have hcap : C1 * S.n * S.D ≤ S.M := by rw [hSn, hM]; exact Nat.le_ceil _
  have hratio : S.badChargeRatio multiplicity ≤ (n : ℝ) ^ (-(kappa / 2)) := by
    calc
      _ ≤ (117 * Real.exp 1 * multiplicity / (2 * C1)) *
          (S.r₀ : ℝ) ^ 3 / S.D :=
        S.badChargeRatio_le_radius_cube multiplicity hC1 hnNat hDpos (hR ▸ hr) hcap
      _ ≤ (n : ℝ) ^ (kappa / 2) / (n : ℝ) ^ kappa := by
        rw [hR]
        gcongr
      _ = _ := by rw [← Real.rpow_sub hnpos]; congr 1; ring
  have hcutNat : 4 * S.r₀ * J ≤ S.D := by
    have hh : (4 : ℝ) * S.r₀ * J ≤ S.D := by rw [hR]; nlinarith [hcut.trans hDR]
    exact_mod_cast hh
  have htail := S.geometricBadTail_le_power (n * S.m) multiplicity J hnR
    (by positivity : 0 ≤ kappa / 2) hcutNat hratio
  obtain ⟨hL, hm'⟩ := CollarScan.source_lengths_le hn hell.le (by linarith : mu ≤ 1)
  have hKn : S.K ≤ n := by rw [hK]; exact (Nat.div_le_self _ _).trans hL
  have hmn : S.m ≤ n := by rwa [hm]
  have hpref := CollarScan.badHistory_prefactor_le hn hKn hL hmn hCt ht
  rw [hSn]
  calc
    _ ≤ ((S.K * 2 * (t + n * ⌊(n : ℝ) ^ (1 - ell)⌋₊) *
          (n * S.m + 1) : ℕ) : ℝ) *
          ((n * S.m + 1 : ℕ) * (n : ℝ) ^ (-(kappa / 2) * J)) := by
      exact mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ 8 * (Ct + 1) * (n : ℝ) ^ 7 * (n : ℝ) ^ (-(kappa / 2) * J) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hpref (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ _ := CollarScan.badHistory_power_le hnR hc hJ'

/-- The finite expression proved from actual ancestry is smaller than every
fixed inverse power at the source scales, uniformly in the scanner and target. -/
theorem eventually_badHistory_bound_le_rpow
    {ell kappa mu Cr C1 Ct : ℝ} (hell : 0 < ell) (hkappa : 0 < kappa)
    (hmu : mu < 1 - ell) (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (p : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type u) (I : Type v) (S : CollarScan V I) (t : ℕ),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n →
      S.M = ⌈C1 * n * S.D⌉₊ → (t : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      ((S.K * 2 * (t + S.n * ⌊(n : ℝ) ^ (1 - ell)⌋₊) *
        (n * S.m + 1) : ℕ) : ℝ) * S.geometricBadTail (n * S.m) multiplicity ≤
        (n : ℝ) ^ (-p) :=
  eventually_atTop.2 ⟨_, fun _ => badHistory_bound_le_rpow_of_threshold_le hell hkappa hmu
    hCr hC1 hCt multiplicity p⟩

end TNLean.PEPS.AreaLaw.Scan

end BadHistoryAsymptotics

section PhysicalBadHistoryDecay

/-!
## Inverse-power probability bounds for actual scan histories

At the source's rounded scales, the probability that any physical scan prefix
has a bad lead decays faster than every fixed inverse power. The result uses
the actual evaluator, uniform labelled charge choices, and lattice ancestry.
Only source geometry assumptions remain: compact target size, ambient row
bounds, target clearance from the cut, and bounded labelled anchor multiplicity.
The exponent 200 in Lemma 9.1 is a specialization of the arbitrary exponent.
Quantum transported states and their entropy gains are separate questions.
The threshold is the explicit `badHistoryThreshold` of the scalar bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 9.1, `08-scanner.tex`, lines 309–329, at `openai/math@adc7f124`.
-/

open Filter
open scoped BigOperators

open ManyBody (ambientDilation planeDomainGraph ambientDepth supDist)

namespace TNLean.PEPS.AreaLaw.Scan

universe u

open Classical in
/-- Lemma 9.1's bad-history estimate for actual finite physical histories, with
an arbitrary decay exponent, at every `n` from the explicit threshold
`badHistoryThreshold kappa Cr C1 Ct multiplicity p` on (`08-scanner.tex`, lines 309–329).
The threshold precedes the domain, target, labels, and scanner. -/
theorem bad_history_probability_le_of_threshold_le
    {ell kappa mu Cr C1 Ct : ℝ} (hell : 0 < ell) (hkappa : 0 < kappa)
    (hkappamu : kappa < mu) (hmu : mu < 1 - ell)
    (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (p : ℝ) {n : ℕ}
    (hthr : badHistoryThreshold kappa Cr C1 Ct multiplicity p ≤ n) :
    ∀ (I : Type u) [Fintype I] [LinearOrder I]
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan ↥Λ I),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n →
      S.M = ⌈C1 * n * S.D⌉₊ → (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = planeDomainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - ell)⌋₊ + 10 * S.r₀ : ℕ) : ℤ) <
          (supDist t z : ℤ)) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      (∑ h : History S.K S.m S.M (n * S.m),
        if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤ (n : ℝ) ^ (-p) := by
  have hscalar := badHistory_bound_le_rpow_of_threshold_le hell hkappa hmu hCr hC1 hCt
    multiplicity p hthr
  have hn3 : 3 ≤ n := (three_le_badHistoryThreshold _ _ _ _ _ _).trans hthr
  have hr := one_le_roundedLogRadius_of_two_le hCr (show 2 ≤ n by omega)
  have hn : 1 ≤ n := by omega
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
  exact (S.sum_historyWeight_bad_through_geometric_planeDomainGraph_le hT hgraph hdepth
    hnNat hmNat (by omega : 0 < S.r₀) hMpos hL hclear hrows hmult).trans
      (hscalar ↥Λ I S T.card hSn hm hK hD hR hM ht)

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
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan ↥Λ I),
      S.n = n → S.m = ⌊(n : ℝ) ^ mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ kappa⌉₊ → S.r₀ = roundedLogRadius Cr n →
      S.M = ⌈C1 * n * S.D⌉₊ → (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = planeDomainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - ell)⌋₊ + 10 * S.r₀ : ℕ) : ℤ) <
          (supDist t z : ℤ)) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      (∑ h : History S.K S.m S.M (n * S.m),
        if ¬ S.IsGoodThrough h then historyWeight h else 0) ≤ (n : ℝ) ^ (-p) :=
  eventually_atTop.2 ⟨_, fun _ => bad_history_probability_le_of_threshold_le hell hkappa hkappamu
    hmu hCr hC1 hCt multiplicity p⟩

end TNLean.PEPS.AreaLaw.Scan

end PhysicalBadHistoryDecay
