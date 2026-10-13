/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyDecay

/-! # Exact uniform source-scale actual charge energy statement -/

set_option autoImplicit false

open scoped BigOperators Matrix
open MeasureTheory Set TensorPower TensorPower.ReplicaTransport Entropy
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

noncomputable section

namespace TNLeanTest.ActualChargeEnergyDecay

open Classical in
/-- One threshold precedes all finite physical and quantum data, while both
history capacities are derived rather than imposed. -/
theorem capstone_signature {Cr C1 Ct : ℝ}
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
                  ((1 - p) * (n : ℝ) ^ (-P) + p)) :=
  exists_actualCharge_energy_threshold hCr hC1 hCt multiplicity P

open Classical in
/-- The same source-scale threshold applies to the zero-replica actual round. -/
theorem zero_replica_signature {Cr C1 Ct : ℝ}
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
          ∀ (a : ℝ), 0 ≤ a → ∀ (pre : (r : ℕ) → Config r
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ),
          pre 0 ∈ symmetricSubspace 0
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) →
          pre 0 ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
          let dims := augmentedDimensions (V := Site Λ) q aux
          let E := S.actualEnergyTerms h Ω Δ
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ aux
          let A : ℝ := 10 * S.K * S.n * S.D * multiplicity
          let ℓ := transportLogDimBound q S.r₀
          (S.actualChargeData hm hM s).energyError E (a / 2) 0 (pre 0) p ≤
            (10 * (S.D : ℝ) / S.m) *
              ((1 - p) * A ^ (7 / 8 : ℝ) *
                (S.actualChargeEntropyDefect hm hM s dims E
                  (a / 2) 0 (pre 0) p) ^ (1 / 8 : ℝ) +
                A * (2 * ℓ) ^ (1 / 8 : ℝ) / 2 *
                  ((1 - p) * (n : ℝ) ^ (-P) + p)) := by
  obtain ⟨N, hN⟩ := exists_actualCharge_energy_threshold hCr hC1 hCt multiplicity P
  refine ⟨N, ?_⟩
  intro n hn Λ T hT R _ S hSn hsm hK hD hr hC ht hgraph hdepth hclear hrows hmult
  obtain ⟨hm, hM, henergy⟩ := hN n hn Λ T hT R S hSn hsm hK hD hr hC ht
    hgraph hdepth hclear hrows hmult
  refine ⟨hm, hM, ?_⟩
  intro q _ aux _ J h Ω Δ s hs a ha pre hsym hpre p hp
  exact henergy q aux J h Ω Δ s hs a ha 0 pre hsym hpre p hp

end TNLeanTest.ActualChargeEnergyDecay
