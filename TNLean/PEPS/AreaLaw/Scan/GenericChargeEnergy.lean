/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyCoefficients

/-!
# Actual charge energy for arbitrary fixed scanner exponents

The established all-time classical tail already allows arbitrary positive
scanner exponents with the source separation inequalities. Its exact old-history
marginal and the supplied-vector energy theorem therefore give the same
physical density-form energy estimate at those exponents. The coefficient
and threshold precede all physical scanners, rounds and vectors.

This extension uses the existing actual histories, labels, probabilities and
energy terms. It does not reconstruct their geometry, select a charge point,
or assume the energy estimate it proves. In particular it is available at the
fixed bootstrap exponents, where the sharp marginal-moment interval fails.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 309--329, 492--520 and 693--755, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.

Validation and inherited-dependency scope:
`docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

open scoped BigOperators Matrix
open Filter MeasureTheory Set TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

universe u

/-- The explicit threshold at arbitrary fixed scanner exponents controlling every classical old
history together with the split-counting margin: the generic form of
`badOldHistoryThreshold`, the larger of the bad-history threshold and the split-counting
threshold at `κ` and `μ` (`08-scanner.tex`, lines 309--329 and 492--520). -/
noncomputable def ScannerExponents.badOldHistoryThreshold (F : ScannerExponents)
    (Cr C1 Ct : ℝ) (multiplicity : ℕ) (P : ℝ) : ℕ :=
  max (badHistoryThreshold F.kappa Cr C1 Ct multiplicity P)
    (splitCountingThreshold Cr F.kappa F.mu)

open Classical in
/-- At arbitrary fixed scanner exponents, every classical old history is controlled and the
split-counting margin holds at every `n` from the explicit threshold
`F.badOldHistoryThreshold Cr C1 Ct multiplicity P` on (`08-scanner.tex`, lines 309--329 and
492--520). -/
theorem ScannerExponents.badOldHistory_of_badOldHistoryThreshold_le (F : ScannerExponents)
    {Cr C1 Ct : ℝ} (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (P : ℝ) {n : ℕ}
    (hthr : F.badOldHistoryThreshold Cr C1 Ct multiplicity P ≤ n) :
    ∀ (I : Type u) [Fintype I] [LinearOrder I]
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan (Site Λ) I),
      S.n = n → S.m = ⌊(n : ℝ) ^ F.mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ F.kappa⌉₊ →
      S.r₀ = roundedLogRadius Cr n → S.C₁ = C1 →
      (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ +
          10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      2 ≤ S.n ∧ S.r₀ ≤ S.D ∧ 1 ≤ S.D ∧
        4 * (S.D + 2 * S.r₀) ≤ S.m ∧
        8 * S.K * S.m ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ ∧
        ∀ s : ℕ, s ≤ S.n * S.m →
          (∑ h : History S.K S.m S.M s,
            if S.IsGoodOldHistory h then 0 else historyWeight h) ≤ (n : ℝ) ^ (-P) := by
  have htail := bad_history_probability_le_of_threshold_le F.ell_pos F.kappa_pos F.kappa_lt_mu
    F.mu_lt_one_sub_ell hCr hC1 hCt multiplicity P ((le_max_left _ _).trans hthr)
  have hscales := split_counting_scale_separation_of_threshold_le
    (ell := F.ell) hCr.le F.kappa_pos F.kappa_lt_mu ((le_max_right _ _).trans hthr)
  intro I _ _ Λ T hT S hSn hm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  have hM : S.M = ⌈C1 * n * S.D⌉₊ := by
    simp only [CollarScan.M, chargeSlotCount, hC, hSn]
  have hfull := htail I Λ T hT S hSn hm hK hD hr hM ht hgraph hdepth hclear hrows hmult
  have hscales' : 2 ≤ S.n ∧ S.r₀ ≤ S.D ∧ 1 ≤ S.D ∧
      4 * (S.D + 2 * S.r₀) ≤ S.m ∧
      8 * S.K * S.m ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ := by
    simpa only [hSn, hm, hK, hD, hr] using hscales
  refine ⟨hscales'.1, hscales'.2.1, hscales'.2.2.1, hscales'.2.2.2.1,
    hscales'.2.2.2.2, ?_⟩
  intro s hs
  have hMpos : 0 < S.M :=
    chargeSlotCount_pos (by simpa only [hC] using hC1) (by omega) hscales'.2.2.1
  exact (S.sum_historyWeight_bad_old_le_bad_through hMpos
    (show s ≤ n * S.m by simpa only [hSn] using hs)).trans hfull

open Classical in
private theorem exists_generic_badOldHistory_threshold (F : ScannerExponents) {Cr C1 Ct : ℝ}
    (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (P : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (I : Type u) [Fintype I] [LinearOrder I]
      (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (S : CollarScan (Site Λ) I),
      S.n = n → S.m = ⌊(n : ℝ) ^ F.mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ F.kappa⌉₊ →
      S.r₀ = roundedLogRadius Cr n → S.C₁ = C1 →
      (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ +
          10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      2 ≤ S.n ∧ S.r₀ ≤ S.D ∧ 1 ≤ S.D ∧
        4 * (S.D + 2 * S.r₀) ≤ S.m ∧
        8 * S.K * S.m ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ ∧
        ∀ s : ℕ, s ≤ S.n * S.m →
          (∑ h : History S.K S.m S.M s,
            if S.IsGoodOldHistory h then 0 else historyWeight h) ≤ (n : ℝ) ^ (-P) :=
  ⟨_, fun _ hn => F.badOldHistory_of_badOldHistoryThreshold_le hCr hC1 hCt multiplicity P hn⟩

open Classical in
private theorem generic_actualCharge_energy_of_threshold_le
    (F : ScannerExponents) {Cr C1 Ct : ℝ}
    (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (P : ℝ) {n : ℕ}
    (hthr : F.badOldHistoryThreshold Cr C1 Ct multiplicity P ≤ n) :
    ∀ (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
      (R : ℕ) [LinearOrder (AdmissibleSupport Λ R)]
      (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)),
      S.n = n → S.m = ⌊(n : ℝ) ^ F.mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ F.kappa⌉₊ →
      S.r₀ = roundedLogRadius Cr n → S.C₁ = C1 →
      (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ +
          10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      ∃ (hm : 0 < S.m) (hM : 0 < S.M),
        ∀ (q : ℕ) [NeZero q] (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
          (J : ℝ) (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
          (s : ℕ), s + 1 ≤ S.n * S.m →
          ∀ (a : ℝ), 0 ≤ a → ∀ (k : ℕ)
          (pre : (r : ℕ) → Config r
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ),
          pre k ∈ symmetricSubspace k
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) →
          pre k ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
          let dims := augmentedDimensions (V := Site Λ) q aux
          let E := S.actualEnergyTerms h Ω Δ
            ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ aux
          let A : ℝ := 10 * S.K * S.n * S.D * multiplicity
          let ℓ := transportLogDimBound q S.r₀
          (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
            (10 * (S.D : ℝ) / S.m) *
              ((1 - p) * A ^ (7 / 8 : ℝ) *
                (S.actualChargeEntropyDefect hm hM s dims E
                  (a / 2) k (pre k) p) ^ (1 / 8 : ℝ) +
                A * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 *
                  ((1 - p) * (n : ℝ) ^ (-P) + p)) := by
  intro Λ T hT R _ S hSn hsm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  obtain ⟨hnS, hrS, hDpos, hmargin, hL, htail⟩ :=
    F.badOldHistory_of_badOldHistoryThreshold_le.{0} hCr hC1 hCt multiplicity P hthr
      (AdmissibleSupport Λ R) Λ T hT S hSn hsm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  have hm : 0 < S.m := by omega
  have hCpos : 0 < S.C₁ := by simpa only [hC] using hC1
  have hM : 0 < S.M := chargeSlotCount_pos hCpos (by omega) hDpos
  refine ⟨hm, hM, ?_⟩
  intro q _ aux _ J h Ω Δ s hs a ha k pre hsym hpre p hp
  let dims := augmentedDimensions (V := Site Λ) q aux
  let E := S.actualEnergyTerms h Ω Δ
    ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ aux
  let A : ℝ := 10 * S.K * S.n * S.D * multiplicity
  let ℓ := transportLogDimBound q S.r₀
  let b := ∑ hist : History S.K S.m S.M s,
    if S.IsGoodOldHistory hist then 0 else historyWeight hist
  have hbad : (1 - p) * b + p ≤ (1 - p) * (n : ℝ) ^ (-P) + p :=
    add_le_add
      (mul_le_mul_of_nonneg_left (htail s (by omega)) (sub_nonneg.mpr hp.2.le)) (le_refl p)
  have hℓ : 0 ≤ ℓ := zero_le_one.trans (one_le_transportLogDimBound (NeZero.pos q) S.r₀)
  calc
    _ ≤ (10 * (S.D : ℝ) / S.m) *
        ((1 - p) * A ^ (7 / 8 : ℝ) *
          (S.actualChargeEntropyDefect hm hM s dims E
            (a / 2) k (pre k) p) ^ (1 / 8 : ℝ) +
          A * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 * ((1 - p) * b + p)) :=
      S.actualCharge_energyError_le_domainGraph hT hgraph hdepth aux h Ω Δ
        hnS hs hrS hDpos hmargin hL hCpos hrows hmult hclear ha k pre hsym hpre hp
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hbad (by positivity)))
        (by positivity)


private theorem charge_energy_coefficient_identity
    {K m n D ℓ μ Q : ℝ} (hK : 0 < K) (hm : 0 < m)
    (hB : 0 < K * n * D) (hℓ : 0 < ℓ) (hμ : 0 ≤ μ) (hQ : 0 ≤ Q)
    (W p z Cen een : ℝ) :
    |Cen| * (W / K) ^ 2 * ℓ ^ een * ((10 * D / m) *
      ((1 - p) * (10 * K * n * D * μ) ^ (7 / 8 : ℝ) * Q ^ (1 / 8 : ℝ) +
        (10 * K * n * D * μ) * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 * z)) =
      W ^ 2 * (n * D ^ 2 / (m * K)) *
        ((10 * (10 * μ) ^ (7 / 8 : ℝ) * |Cen| * ℓ ^ een) *
          ((1 - p) * (Q / (K * n * D)) ^ (1 / 8 : ℝ)) +
          (50 * μ * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen| * ℓ ^ (een + 1 / 8)) * z) := by
  have hA : (10 * K * n * D * μ) ^ (7 / 8 : ℝ) =
      (10 * μ) ^ (7 / 8 : ℝ) * (K * n * D) ^ (7 / 8 : ℝ) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 10 * μ) hB.le]
    congr 1
    ring
  have hQroot : Q ^ (1 / 8 : ℝ) =
      (K * n * D) ^ (1 / 8 : ℝ) * (Q / (K * n * D)) ^ (1 / 8 : ℝ) := by
    rw [← Real.mul_rpow hB.le (div_nonneg hQ hB.le), _root_.mul_div_cancel₀ Q hB.ne']
  have hBroot : (K * n * D) ^ (7 / 8 : ℝ) *
      (K * n * D) ^ (1 / 8 : ℝ) = K * n * D := by
    rw [← Real.rpow_add hB]
    norm_num
  have hgood : (10 * K * n * D * μ) ^ (7 / 8 : ℝ) * Q ^ (1 / 8 : ℝ) =
      (10 * μ) ^ (7 / 8 : ℝ) * (K * n * D) *
        (Q / (K * n * D)) ^ (1 / 8 : ℝ) := by
    rw [hA, hQroot]
    calc
      _ = (10 * μ) ^ (7 / 8 : ℝ) *
          ((K * n * D) ^ (7 / 8 : ℝ) * (K * n * D) ^ (1 / 8 : ℝ)) *
          (Q / (K * n * D)) ^ (1 / 8 : ℝ) := by ring
      _ = _ := by rw [hBroot]
  rw [_root_.mul_assoc (1 - p) _ (Q ^ (1 / 8 : ℝ)), hgood,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hℓ.le, Real.rpow_add hℓ]
  field_simp [hK.ne', hm.ne']; ring

/-- The explicit threshold of the actual charge-energy coefficients at arbitrary fixed scanner
exponents: the bad-old-history threshold, the scale-facts threshold, and `n ≥ 3`, so that
`log n ≥ 1` (`08-scanner.tex`, lines 32--42, 309--329 and 492--520). -/
noncomputable def ScannerExponents.actualChargeEnergyThreshold (F : ScannerExponents)
    (Cr C1 Ct : ℝ) (multiplicity : ℕ) (P : ℝ) : ℕ :=
  max (F.badOldHistoryThreshold Cr C1 Ct multiplicity P) (max F.scaleFactsThreshold 3)

open Classical in
/-- Physical charge-energy bound at arbitrary fixed scanner exponents with the explicit
coefficient `actualChargeEnergyCoefficient q Cr multiplicity Cen een` and logarithmic exponent
`transportLogExponent een (een + 1 / 8)`, at every `n` from the explicit threshold
`F.actualChargeEnergyThreshold Cr C1 Ct multiplicity P` on.
Source: `08-scanner.tex`, lines 492--520 and the bootstrap in lines 693--755. -/
theorem ScannerExponents.actualCharge_energy_coefficients_of_threshold_le
    (F : ScannerExponents) (q : ℕ) [NeZero q]
    {Cr C1 Ct : ℝ} (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (P Cen een : ℝ) {n : ℕ}
    (hthr : F.actualChargeEnergyThreshold Cr C1 Ct multiplicity P ≤ n) :
      ∀ (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
      (R : ℕ) [LinearOrder (AdmissibleSupport Λ R)]
      (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)),
      S.n = n → S.m = ⌊(n : ℝ) ^ F.mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ F.kappa⌉₊ →
      S.r₀ = roundedLogRadius Cr n → S.C₁ = C1 →
      (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ +
          10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      ∃ (hm : 0 < S.m) (hM : 0 < S.M),
        ∀ (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
          (J : ℝ) (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
          (s : ℕ), s + 1 ≤ S.n * S.m →
          ∀ (W : ℝ), 0 ≤ W → ∀ (k : ℕ)
          (pre : (r : ℕ) → Config r
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ),
          pre k ∈ symmetricSubspace k
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) →
          pre k ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
          let a := W / (S.K : ℝ)
          let dims := augmentedDimensions (V := Site Λ) q aux
          let E := S.actualEnergyTerms h Ω Δ
            ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ aux
          let ℓ := transportLogDimBound q S.r₀
          |Cen| * a ^ 2 * ℓ ^ een *
            (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
              actualChargeEnergyCoefficient q Cr multiplicity Cen een * W ^ 2 *
                (n : ℝ) ^ F.ell * (S.D : ℝ) ^ 2 *
                (Real.log n) ^ transportLogExponent een (een + 1 / 8) *
                ((1 - p) * (S.actualChargeEntropyDefect hm hM s dims E
                  (a / 2) k (pre k) p / (S.K * n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                  (1 - p) * (n : ℝ) ^ (-P) + p) := by
  simp only [actualChargeEnergyThreshold, max_le_iff] at hthr
  obtain ⟨hbad, hsf, hn3⟩ := hthr
  obtain ⟨hCd, -, hcoeff⟩ := transport_coefficients_log_bound (NeZero.pos q) hCr.le
    (10 * (10 * (multiplicity : ℝ)) ^ (7 / 8 : ℝ) * |Cen|) een
    (50 * (multiplicity : ℝ) * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen|) (een + 1 / 8)
  have hF := scaleFacts_of_scaleFactsThreshold_le F hsf
  have hlogn := Real.one_le_log_natCast_of_three_le hn3
  rw [actualChargeEnergyCoefficient]
  generalize transportLogCoefficient q Cr _ een _ (een + 1 / 8) = Cd at hCd hcoeff ⊢
  generalize transportLogExponent een (een + 1 / 8) = Cl at hcoeff ⊢
  generalize (32 : ℝ) = Cs at hF ⊢
  intro Λ T hT R _ S hSn hsm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  obtain ⟨hm, hM, henergy⟩ := generic_actualCharge_energy_of_threshold_le F hCr hC1 hCt
    multiplicity P hbad Λ T hT R S hSn hsm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  have hmX : S.m = F.m n := hsm
  have hKX : S.K = F.K n := by
    simpa only [ScannerExponents.K, ScannerExponents.L, hmX] using hK
  have hDX : S.D = F.D n := hD
  have hKpos : (0 : ℝ) < S.K := by
    exact_mod_cast (show 0 < S.K by rw [hKX]; exact lt_of_lt_of_le Nat.zero_lt_one hF.one_le_K)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hF.two_le_n; omega)
  have hDpos : (0 : ℝ) < S.D := by
    exact_mod_cast (show 0 < S.D by rw [hDX]; exact lt_of_lt_of_le Nat.zero_lt_one hF.one_le_D)
  have hmpos : (0 : ℝ) < S.m := by exact_mod_cast hm
  have hscale : (n : ℝ) * (S.D : ℝ) ^ 2 / (S.m * S.K : ℝ) ≤
      Cs * (n : ℝ) ^ F.ell * (S.D : ℝ) ^ 2 := by
    simpa only [hmX, hKX, hDX] using hF.coefficient_le
  refine ⟨hm, hM, ?_⟩
  intro aux _ J h Ω Δ s hs W hW k pre hsym hpre p hp
  let a := W / (S.K : ℝ)
  let dims := augmentedDimensions (V := Site Λ) q aux
  let E := S.actualEnergyTerms h Ω Δ
    ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ aux
  let ℓ := transportLogDimBound q S.r₀
  let Q := S.actualChargeEntropyDefect hm hM s dims E (a / 2) k (pre k) p
  let B : ℝ := S.K * n * S.D
  let U := (1 - p) * (Q / B) ^ (1 / 8 : ℝ)
  let Z := (1 - p) * (n : ℝ) ^ (-P) + p
  have ha : 0 ≤ a := div_nonneg hW hKpos.le
  have hℓ : 1 ≤ ℓ := one_le_transportLogDimBound (NeZero.pos q) S.r₀
  have hℓpos : 0 < ℓ := zero_lt_one.trans_le hℓ
  have hQ : 0 ≤ Q := S.actualChargeEntropyDefect_nonneg hm hM s dims E ha k pre p
  have hB : 0 < B := mul_pos (mul_pos hKpos hnpos) hDpos
  have hU : 0 ≤ U := mul_nonneg (sub_nonneg.mpr hp.2.le)
    (Real.rpow_nonneg (div_nonneg hQ hB.le) _)
  have hZ : 0 ≤ Z := add_nonneg
    (mul_nonneg (sub_nonneg.mpr hp.2.le) (Real.rpow_nonneg hnpos.le _)) hp.1.le
  obtain ⟨hcgood, hcbad⟩ := hcoeff n hlogn ℓ hℓ (by simp only [ℓ, hr]; exact le_rfl)
  have hcombined :
      (10 * (10 * (multiplicity : ℝ)) ^ (7 / 8 : ℝ) * |Cen| * ℓ ^ een) * U +
        (50 * (multiplicity : ℝ) * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen| *
          ℓ ^ (een + 1 / 8)) * Z ≤ Cd * (Real.log n) ^ Cl * (U + Z) := by
    calc
      _ ≤ (Cd * (Real.log n) ^ Cl) * U + (Cd * (Real.log n) ^ Cl) * Z :=
        add_le_add (mul_le_mul_of_nonneg_right hcgood hU)
          (mul_le_mul_of_nonneg_right hcbad hZ)
      _ = _ := by ring
  calc
    _ ≤ |Cen| * a ^ 2 * ℓ ^ een * ((10 * (S.D : ℝ) / S.m) *
        ((1 - p) * (10 * S.K * n * S.D * multiplicity : ℝ) ^ (7 / 8 : ℝ) *
          Q ^ (1 / 8 : ℝ) + (10 * S.K * n * S.D * multiplicity : ℝ) *
          (2 * ℓ) ^ (1 / 8 : ℝ) / 2 * Z)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [hSn] using henergy q aux J h Ω Δ s hs a ha k pre hsym hpre p hp)
        (by positivity)
    _ = W ^ 2 * ((n : ℝ) * (S.D : ℝ) ^ 2 / (S.m * S.K : ℝ)) *
        ((10 * (10 * (multiplicity : ℝ)) ^ (7 / 8 : ℝ) * |Cen| * ℓ ^ een) * U +
          (50 * (multiplicity : ℝ) * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen| *
            ℓ ^ (een + 1 / 8)) * Z) :=
      charge_energy_coefficient_identity hKpos hmpos hB hℓpos (Nat.cast_nonneg _) hQ
        W p Z Cen een
    _ ≤ W ^ 2 * ((n : ℝ) * (S.D : ℝ) ^ 2 / (S.m * S.K : ℝ)) *
        (Cd * (Real.log n) ^ Cl * (U + Z)) :=
      mul_le_mul_of_nonneg_left hcombined (by positivity)
    _ ≤ W ^ 2 * (Cs * (n : ℝ) ^ F.ell * (S.D : ℝ) ^ 2) *
        (Cd * (Real.log n) ^ Cl * (U + Z)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (sq_nonneg W))
        (by positivity)
    _ = _ := by dsimp only [U, Z, Q, B]; ring


open Classical in
/-- Uniform physical charge-energy coefficients for any fixed source scanner
exponents. The exact original history probabilities, label multiplicity and
supplied symmetric vector are retained. There is no marginal-moment assumption.
Source: `08-scanner.tex`, lines 492--520 and the bootstrap in lines 693--755. -/
theorem ScannerExponents.exists_actualCharge_energy_coefficients
    (F : ScannerExponents) (q : ℕ) [NeZero q]
    {Cr C1 Ct : ℝ} (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (P Cen een : ℝ) :
    ∃ C Cl : ℝ, 1 ≤ C ∧ 0 ≤ Cl ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
      (R : ℕ) [LinearOrder (AdmissibleSupport Λ R)]
      (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)),
      S.n = n → S.m = ⌊(n : ℝ) ^ F.mu⌋₊ →
      S.K = ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ / (8 * S.m) →
      S.D = ⌈(n : ℝ) ^ F.kappa⌉₊ →
      S.r₀ = roundedLogRadius Cr n → S.C₁ = C1 →
      (T.card : ℝ) ≤ Ct * (n : ℝ) ^ 2 →
      S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
      (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
        ((2 * ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ +
          10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
      (∀ d : ℕ, 1 ≤ d → d ≤ ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ →
        (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ multiplicity) →
      ∃ (hm : 0 < S.m) (hM : 0 < S.M),
        ∀ (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
          (J : ℝ) (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q) (Δ : ℝ)
          (s : ℕ), s + 1 ≤ S.n * S.m →
          ∀ (W : ℝ), 0 ≤ W → ∀ (k : ℕ)
          (pre : (r : ℕ) → Config r
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ),
          pre k ∈ symmetricSubspace k
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) →
          pre k ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
          let a := W / (S.K : ℝ)
          let dims := augmentedDimensions (V := Site Λ) q aux
          let E := S.actualEnergyTerms h Ω Δ
            ⌊(n : ℝ) ^ (1 - F.ell)⌋₊ aux
          let ℓ := transportLogDimBound q S.r₀
          |Cen| * a ^ 2 * ℓ ^ een *
            (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
              C * W ^ 2 * (n : ℝ) ^ F.ell *
                (S.D : ℝ) ^ 2 * (Real.log n) ^ Cl *
                ((1 - p) * (S.actualChargeEntropyDefect hm hM s dims E
                  (a / 2) k (pre k) p / (S.K * n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                  (1 - p) * (n : ℝ) ^ (-P) + p) :=
  have h := transport_coefficients_log_bound (NeZero.pos q) hCr.le
    (10 * (10 * (multiplicity : ℝ)) ^ (7 / 8 : ℝ) * |Cen|) een
    (50 * (multiplicity : ℝ) * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen|) (een + 1 / 8)
  ⟨_, _, one_le_mul_of_one_le_of_one_le (by norm_num) h.1, h.2.1, _,
    fun _ hn => F.actualCharge_energy_coefficients_of_threshold_le q hCr hC1 hCt multiplicity
      P Cen een hn⟩

end TNLean.PEPS.AreaLaw.Scan
