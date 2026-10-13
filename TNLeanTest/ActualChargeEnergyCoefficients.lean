/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEnergyCoefficients

/-! # Actual charge coefficient and boundary regressions -/

set_option autoImplicit false

open scoped BigOperators Matrix
open MeasureTheory Set TensorPower TensorPower.ReplicaTransport Entropy
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

noncomputable section

namespace TNLeanTest.ActualChargeEnergyCoefficients

open Classical in
/-- Constants precede every physical, quantum and interpolation input. -/
theorem capstone_signature (q : ℕ) [NeZero q]
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
                  (1 - p) * (n : ℝ) ^ (-P) + p) :=
  exists_actualCharge_energy_coefficients q hCr hC1 hCt multiplicity P Cen een

open Classical in
/-- The literal zero-copy charge uses the same uniform coefficients. -/
theorem zero_replica_signature (q : ℕ) [NeZero q]
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
          ∀ (W : ℝ), 0 ≤ W → ∀ (pre : (r : ℕ) → Config r
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ),
          pre 0 ∈ symmetricSubspace 0
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) →
          pre 0 ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
          let a := W / (S.K : ℝ)
          let dims := augmentedDimensions (V := Site Λ) q aux
          let E := S.actualEnergyTerms h Ω Δ
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ aux
          let ℓ := transportLogDimBound q S.r₀
          |Cen| * a ^ 2 * ℓ ^ een *
            (S.actualChargeData hm hM s).energyError E (a / 2) 0 (pre 0) p ≤
              C * W ^ 2 * (n : ℝ) ^ (Exponents.scannerEll : ℝ) *
                (S.D : ℝ) ^ 2 * (Real.log n) ^ Cl *
                ((1 - p) * (S.actualChargeEntropyDefect hm hM s dims E
                  (a / 2) 0 (pre 0) p / (S.K * n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                  (1 - p) * (n : ℝ) ^ (-P) + p) := by
  obtain ⟨C, Cl, hC, hCl, N, hN⟩ :=
    exists_actualCharge_energy_coefficients q hCr hC1 hCt multiplicity P Cen een
  refine ⟨C, Cl, hC, hCl, N, ?_⟩
  intro n hn Λ T hT R _ S hSn hsm hK hD hr hC1eq ht hgraph hdepth hclear hrows hmult
  obtain ⟨hm, hM, henergy⟩ :=
    hN n hn Λ T hT R S hSn hsm hK hD hr hC1eq ht hgraph hdepth hclear hrows hmult
  refine ⟨hm, hM, ?_⟩
  intro aux _ J h Ω Δ s hs W hW pre hsym hpre p hp
  exact henergy aux J h Ω Δ s hs W hW 0 pre hsym hpre p hp

open Classical in
/-- Dimension one and zero labelled capacity coexist with a negative exponent. -/
theorem boundary_signature
    {Cr C1 Ct : ℝ} (hCr : 0 < Cr) (hC1 : 0 < C1) (hCt : 0 ≤ Ct)
    (P Cen : ℝ) :
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
      (∀ y, (Finset.univ.filter fun i ↦ S.anchor i = y).card ≤ 0) →
      ∃ (hm : 0 < S.m) (hM : 0 < S.M),
        ∀ (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
          (J : ℝ) (h : LocalHamiltonian Λ 1 R J) (Ω : StateSpace Λ 1) (Δ : ℝ)
          (s : ℕ), s + 1 ≤ S.n * S.m →
          ∀ (W : ℝ), 0 ≤ W → ∀ (k : ℕ)
          (pre : (r : ℕ) → Config r
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) 1 aux v)) → ℂ),
          pre k ∈ symmetricSubspace k
            (fun v ↦ Fin (augmentedDimensions (V := Site Λ) 1 aux v)) →
          pre k ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
          let a := W / (S.K : ℝ)
          let dims := augmentedDimensions (V := Site Λ) 1 aux
          let E := S.actualEnergyTerms h Ω Δ
            ⌊(n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ aux
          let ℓ := transportLogDimBound 1 S.r₀
          |Cen| * a ^ 2 * ℓ ^ (-3 : ℝ) *
            (S.actualChargeData hm hM s).energyError E (a / 2) k (pre k) p ≤
              C * W ^ 2 * (n : ℝ) ^ (Exponents.scannerEll : ℝ) *
                (S.D : ℝ) ^ 2 * (Real.log n) ^ Cl *
                ((1 - p) * (S.actualChargeEntropyDefect hm hM s dims E
                  (a / 2) k (pre k) p / (S.K * n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                  (1 - p) * (n : ℝ) ^ (-P) + p) :=
  exists_actualCharge_energy_coefficients 1 hCr hC1 hCt 0 P Cen (-3)

open Classical in
/-- Literal defect nonnegativity needs neither vector normalization nor a sign of p. -/
theorem defect_nonneg_signature
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (dims : V ⊕ Bool → ℕ) [∀ v, NeZero (dims v)]
    (E : EnergyTerms (V ⊕ Bool) dims I) {a : ℝ} (ha : 0 ≤ a) (k : ℕ)
    (pre : (r : ℕ) → Config r (fun v ↦ Fin (dims v)) → ℂ) (p : ℝ) :
    0 ≤ S.actualChargeEntropyDefect hm hM s dims E (a / 2) k (pre k) p :=
  S.actualChargeEntropyDefect_nonneg hm hM s dims E ha k pre p

/-- Zero total weight annihilates the exact actual energy expression. -/
theorem zero_weight_signature
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M) (s : ℕ)
    (dims : V ⊕ Bool → ℕ) [∀ v, NeZero (dims v)]
    (E : EnergyTerms (V ⊕ Bool) dims I) (Cen een ℓ : ℝ) (k : ℕ)
    (pre : Config k (fun v ↦ Fin (dims v)) → ℂ) (p : ℝ) :
    |Cen| * (0 / (S.K : ℝ)) ^ 2 * ℓ ^ een *
      (S.actualChargeData hm hM s).energyError E ((0 / S.K) / 2) k pre p = 0 := by
  simp

end TNLeanTest.ActualChargeEnergyCoefficients
