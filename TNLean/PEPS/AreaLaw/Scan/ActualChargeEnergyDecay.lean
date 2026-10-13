/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyBound
import TNLean.PEPS.AreaLaw.Scan.BadOldHistoryDecay

/-!
# Actual charge energy at the fixed scanner scales

The same actual energy and entropy defect obey the finite charge estimate with
the classical bad-old mass replaced by any fixed inverse power of n. One
threshold supplies both that tail bound and the split-counting margin, before
the physical scanner, round, replica count, auxiliary dimensions, supplied
vector and common interpolation parameter are specified.

The literal capacity 10KnD times the anchor multiplicity remains explicit.
The vector is supplied, symmetric and nonzero; no physical prevector identity
or norm comparison is assumed or concluded. No charge round is selected.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 492–511 and `scanner:final-parameters`, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators Matrix
open MeasureTheory Set TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

open Classical in
/-- At the fixed source scales, the literal charge energy has an arbitrarily
small inverse-power old-history error, uniformly over all admissible charges
and supplied vectors. Positivity of both history capacities is derived.
Source: `08-scanner.tex`, lines 492–511 and `scanner:final-parameters`. -/
theorem exists_actualCharge_energy_threshold {Cr C1 Ct : ℝ}
    (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (multiplicity : ℕ) (P : ℝ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty)
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
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ aux
          let A : ℝ := 10 * S.K * S.n * S.D * multiplicity
          let ℓ := transportLogDimBound q S.r₀
          (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
            (10 * (S.D : ℝ) / S.m) *
              ((1 - p) * A ^ (7 / 8 : ℝ) *
                (S.actualChargeEntropyDefect hm hM s dims E
                  (a / 2) k (pre k) p) ^ (1 / 8 : ℝ) +
                A * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 *
                  ((1 - p) * (n : ℝ) ^ (-P) + p)) := by
  obtain ⟨N, hN⟩ := exists_badOldHistory_threshold.{0} hCr hC1 hCt multiplicity P
  refine ⟨N, ?_⟩
  intro n hn Λ T hT R _ S hSn hsm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  obtain ⟨hnS, hrS, hDpos, hmargin, hL, htail⟩ :=
    hN n hn (AdmissibleSupport Λ R) Λ T hT S hSn hsm hK hD hr hC ht
      hgraph hdepth hclear hrows hmult
  have hm : 0 < S.m := by omega
  have hCpos : 0 < S.C₁ := by simpa only [hC] using hC1
  have hM : 0 < S.M := chargeSlotCount_pos hCpos (by omega) hDpos
  refine ⟨hm, hM, ?_⟩
  intro q _ aux _ J h Ω Δ s hs a ha k pre hsym hpre p hp
  let dims := augmentedDimensions (V := Site Λ) q aux
  let E := S.actualEnergyTerms h Ω Δ
    ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ aux
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

end TNLean.PEPS.AreaLaw.Scan
