/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyDecay
import TNLean.PEPS.AreaLaw.Scan.Budgets
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimensionScale

/-!
# Uniform coefficients for the actual charge energy

The supplied-vector charge estimate has fixed coefficients after the rate is
written as `W / K`. The entropy defect is the literal good-old-history integral;
its nonnegativity follows from the actual leaf measures and split entropies.
The rounded scales give positive K and absorb `n D² / (m K)` into `n^ℓ D²`.
The two remaining physical dimension factors have one logarithmic-power cap.

All constants and the threshold precede the physical scanner, round, auxiliary
dimensions, supplied vector, nonnegative weight and interpolation parameter.
Zero weight, zero anchor multiplicity, one-dimensional physical sites and zero
replicas remain allowed. No charge round or entropy defect is selected.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 492–520 and `scanner:final-parameters`, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators Matrix
open Filter MeasureTheory Set TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open Classical in
/-- The actual good-old defect is nonnegative for every supplied vector and
every interpolation parameter. Source: `08-scanner.tex`, lines 424–429. -/
theorem CollarScan.actualChargeEntropyDefect_nonneg
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (dims : V ⊕ Bool → ℕ) [∀ v, NeZero (dims v)]
    (E : EnergyTerms (V ⊕ Bool) dims I) {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : (r : ℕ) → Config r (fun v ↦ Fin (dims v)) → ℂ) (p : ℝ) :
    0 ≤ S.actualChargeEntropyDefect hm hM s dims E (a / 2) k (pre k) p := by
  rw [← S.actualChargeScanRound_chargeDefect hm hM s dims E a pre ha k p]
  unfold ScanRound.chargeDefect
  apply Finset.sum_nonneg
  intro hist _
  split_ifs
  · apply mul_nonneg
    · change 0 ≤ (S.actualChargeData hm hM s).histTree.weight hist
      rw [show (S.actualChargeData hm hM s).histTree.weight hist = historyWeight hist from
        historyMeanTree_weight S.K S.m S.M hm hM s hist]
      exact historyWeight_nonneg hist
    · apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact integral_nonneg fun θ ↦
          (S.actualChargeData hm hM s).splitEta_nonneg dims E
            (S.actualChargeData_isAdmissible hm hM s) i ⟨hist, none⟩ θ.1
      · exact le_rfl
  · exact le_rfl

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

open Classical in
/-- The actual charge error has uniform logarithmic coefficients at the fixed
rounded scales. The density is the same literal defect divided by `KnD`;
its sign and the positivity of K follow internally. The real coefficient and
exponent may have either sign. Source: `08-scanner.tex`, lines 492–520. -/
theorem exists_actualCharge_energy_coefficients (q : ℕ) [NeZero q]
    {Cr C1 Ct : ℝ} (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (P Cen een : ℝ) :
    ∃ C Cl : ℝ, 1 ≤ C ∧ 0 ≤ Cl ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
      (R : ℕ) [LinearOrder (AdmissibleSupport Λ R)]
      (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)),
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
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ aux
          let ℓ := transportLogDimBound q S.r₀
          |Cen| * a ^ 2 * ℓ ^ een *
            (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
              C * W ^ 2 * (n : ℝ) ^ (Exponents.scannerEll : ℝ) *
                (S.D : ℝ) ^ 2 * (Real.log n) ^ Cl *
                ((1 - p) * (S.actualChargeEntropyDefect hm hM s dims E
                  (a / 2) k (pre k) p / (S.K * n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                  (1 - p) * (n : ℝ) ^ (-P) + p) := by
  let X : ScannerExponents :=
    { ell := (Exponents.scannerEll : ℝ)
      kappa := (Exponents.scannerKappa : ℝ)
      mu := (Exponents.scannerMu : ℝ)
      nu := (Exponents.scannerNu : ℝ)
      e := (Exponents.boxError : ℝ)
      ell_pos := by norm_num [Exponents.scannerEll]
      ell_lt_one := by norm_num [Exponents.scannerEll]
      kappa_pos := by norm_num [Exponents.scannerKappa]
      kappa_lt_mu := by norm_num [Exponents.scannerKappa, Exponents.scannerMu]
      mu_lt_one_sub_ell := by norm_num [Exponents.scannerMu, Exponents.scannerEll]
      nu_pos := by norm_num [Exponents.scannerNu]
      e_pos := by norm_num [Exponents.boxError]
      e_lt_one := by norm_num [Exponents.boxError]
      kappa_le_e := by norm_num [Exponents.scannerKappa, Exponents.boxError] }
  obtain ⟨Cs, hscales⟩ := eventually_scaleFacts X
  obtain ⟨n₀, hn₀⟩ := hscales.exists
  have hCs : 1 ≤ Cs := hn₀.one_le_C₁
  obtain ⟨Cd, Cl, hCd, hCl, hcoeff⟩ := exists_transport_coefficients_log_bound
    (NeZero.pos q) hCr.le
    (10 * (10 * (multiplicity : ℝ)) ^ (7 / 8 : ℝ) * |Cen|) een
    (50 * (multiplicity : ℝ) * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen|) (een + 1 / 8)
  obtain ⟨Ne, hNe⟩ := exists_actualCharge_energy_threshold hCr hC1 hCt multiplicity P
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp (hscales.and hlog)
  refine ⟨Cs * Cd, Cl, one_le_mul_of_one_le_of_one_le hCs hCd, hCl,
    max Ne Ns, ?_⟩
  intro n hn Λ T hT R _ S hSn hsm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  obtain ⟨hF, hlogn⟩ := hNs n ((le_max_right Ne Ns).trans hn)
  obtain ⟨hm, hM, henergy⟩ := hNe n ((le_max_left Ne Ns).trans hn)
    Λ T hT R S hSn hsm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  have hmX : S.m = X.m n := hsm
  have hKX : S.K = X.K n := by
    simpa only [ScannerExponents.K, ScannerExponents.L, hmX] using hK
  have hDX : S.D = X.D n := hD
  have hKpos : (0 : ℝ) < S.K := by
    exact_mod_cast (show 0 < S.K by rw [hKX]; exact lt_of_lt_of_le Nat.zero_lt_one hF.one_le_K)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hF.two_le_n; omega)
  have hDpos : (0 : ℝ) < S.D := by
    exact_mod_cast (show 0 < S.D by rw [hDX]; exact lt_of_lt_of_le Nat.zero_lt_one hF.one_le_D)
  have hmpos : (0 : ℝ) < S.m := by exact_mod_cast hm
  have hscale : (n : ℝ) * (S.D : ℝ) ^ 2 / (S.m * S.K : ℝ) ≤
      Cs * (n : ℝ) ^ (Exponents.scannerEll : ℝ) * (S.D : ℝ) ^ 2 := by
    simpa only [hmX, hKX, hDX] using hF.coefficient_le
  refine ⟨hm, hM, ?_⟩
  intro aux _ J h Ω Δ s hs W hW k pre hsym hpre p hp
  let a := W / (S.K : ℝ)
  let dims := augmentedDimensions (V := Site Λ) q aux
  let E := S.actualEnergyTerms h Ω Δ
    ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ aux
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
    _ ≤ W ^ 2 * (Cs * (n : ℝ) ^ (Exponents.scannerEll : ℝ) * (S.D : ℝ) ^ 2) *
        (Cd * (Real.log n) ^ Cl * (U + Z)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (sq_nonneg W))
        (by positivity)
    _ = _ := by dsimp only [U, Z, Q, B]; ring

end TNLean.PEPS.AreaLaw.Scan
