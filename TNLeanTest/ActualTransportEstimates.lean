/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTransportEstimates

/-!
# Actual transport signatures, uniformity and endpoints

The complete type regressions fix all four conclusions and all quantitative
factors, with universal constants before physical data and the same error
sequences for every replica count, vector, interpolation point and eigenvalue.
No admissibility, support, commutation or dimension certificate is an input.

The endpoint regressions separately apply the integral conclusion at 0 and 1
and on every degenerate closed subinterval. The replica count is unrestricted,
so these tests retain the zero-replica convention. No vector is constructed.
-/

set_option autoImplicit false

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open TensorPower TensorPower.ReplicaTransport

noncomputable section
namespace TNLeanTest.ActualTransportEstimates

-- Exact fill signature, including every error factor and the actual Hamiltonian.
example :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {s L : ℕ} (hn : 0 < S.n), s + 1 ≤ S.n * S.m → S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hC : 0 < S.C₁),
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
        let n := augmentedDimensions (V := Site Λ) q aux
        let D := S.actualFillData hm hM s
        let E := S.actualEnergyTerms h Ω Δ L aux
        let ℓ := transportLogDimBound q S.r₀
        let Hbar := fun r => copyMean n r
          (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i))
        ∃ β ε : ℕ → ℝ, (β =O[atTop] fun r : ℕ => Real.log (r + 1)) ∧
          Tendsto ε atTop (𝓝 0) ∧
          ∀ (r : ℕ) (pre : Config r (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace r (fun v => Fin (n v)) → pre ≠ 0 →
            (∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun p' => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p') pre))
                (D.exactDerivative n (a / 2) r pre p) p ∧
              (r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                  Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r ≤
                D.exactDerivative n (a / 2) r pre p ∧
              ∀ E₀ : ℝ, Hbar r *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector (D.rootPath n (a / 2) r p) pre
                (star v ⬝ᵥ (Hbar r *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) r pre p + ε r) ∧
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              ∫ p in p₀..p₁, ((r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                  Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r) ≤
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₀) pre) -
                  Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₁) pre) :=
  CollarScan.actualFill_transport_domainGraph

-- Exact charge signature, including every error factor and the actual Hamiltonian.
example :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {s L : ℕ} (hn : 0 < S.n), s + 1 ≤ S.n * S.m → S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hC : 0 < S.C₁),
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
        let n := augmentedDimensions (V := Site Λ) q aux
        let D := S.actualChargeData hm hM s
        let E := S.actualEnergyTerms h Ω Δ L aux
        let ℓ := transportLogDimBound q S.r₀
        let Hbar := fun r => copyMean n r
          (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i))
        ∃ β ε : ℕ → ℝ, (β =O[atTop] fun r : ℕ => Real.log (r + 1)) ∧
          Tendsto ε atTop (𝓝 0) ∧
          ∀ (r : ℕ) (pre : Config r (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace r (fun v => Fin (n v)) → pre ≠ 0 →
            (∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun p' => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p') pre))
                (D.exactDerivative n (a / 2) r pre p) p ∧
              (r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                  Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r ≤
                D.exactDerivative n (a / 2) r pre p ∧
              ∀ E₀ : ℝ, Hbar r *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector (D.rootPath n (a / 2) r p) pre
                (star v ⬝ᵥ (Hbar r *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) r pre p + ε r) ∧
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              ∫ p in p₀..p₁, ((r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                  Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r) ≤
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₀) pre) -
                  Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₁) pre) :=
  CollarScan.actualCharge_transport_domainGraph

-- Fill endpoints, with one sequence uniform over all replicas and supplied vectors.
example :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {s L : ℕ} (hn : 0 < S.n), s + 1 ≤ S.n * S.m → S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hC : 0 < S.C₁),
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
        let n := augmentedDimensions (V := Site Λ) q aux
        let D := S.actualFillData hm hM s
        let ℓ := transportLogDimBound q S.r₀
        ∃ β : ℕ → ℝ, (β =O[atTop] fun r : ℕ => Real.log (r + 1)) ∧
          ∀ (r : ℕ) (pre : Config r (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace r (fun v => Fin (n v)) → pre ≠ 0 →
            (∫ p in (0 : ℝ)..1, ((r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r) ≤
              Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r 0) pre) -
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r 1) pre)) ∧
            ∀ p₀ ∈ Icc (0 : ℝ) 1,
              (∫ p in p₀..p₀, ((r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r)) ≤ 0 := by
  obtain ⟨c₀, Cent, eent, _, _, hc₀, htransport⟩ :=
    CollarScan.actualFill_transport_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    s L hn hs hr hDpos hD hL hC hrows hclear a ha haℓ
  obtain ⟨β, _, hβ, _, hresult⟩ := htransport aux h Ω S hT hgraph hdepth hanchor
    hΔ hΩ hn hs hr hDpos hD hL hC hrows hclear ha haℓ
  refine ⟨β, hβ, ?_⟩
  intro r pre hpre hne
  have hint := (hresult r pre hpre hne).2
  refine ⟨hint 0 1 (le_refl 0) zero_le_one (le_refl 1), ?_⟩
  intro p₀ hp₀
  simpa only [sub_self] using hint p₀ p₀ hp₀.1 (le_refl p₀) hp₀.2

-- Charge endpoints, with one sequence uniform over all replicas and supplied vectors.
example :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {s L : ℕ} (hn : 0 < S.n), s + 1 ≤ S.n * S.m → S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hC : 0 < S.C₁),
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
        let n := augmentedDimensions (V := Site Λ) q aux
        let D := S.actualChargeData hm hM s
        let ℓ := transportLogDimBound q S.r₀
        ∃ β : ℕ → ℝ, (β =O[atTop] fun r : ℕ => Real.log (r + 1)) ∧
          ∀ (r : ℕ) (pre : Config r (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace r (fun v => Fin (n v)) → pre ≠ 0 →
            (∫ p in (0 : ℝ)..1, ((r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r) ≤
              Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r 0) pre) -
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r 1) pre)) ∧
            ∀ p₀ ∈ Icc (0 : ℝ) 1,
              (∫ p in p₀..p₀, ((r : ℝ) * a * D.entropyGain n (a / 2) r pre p -
                Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r)) ≤ 0 := by
  obtain ⟨c₀, Cent, eent, _, _, hc₀, htransport⟩ :=
    CollarScan.actualCharge_transport_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    s L hn hs hr hDpos hD hL hC hrows hclear a ha haℓ
  obtain ⟨β, _, hβ, _, hresult⟩ := htransport aux h Ω S hT hgraph hdepth hanchor
    hΔ hΩ hn hs hr hDpos hD hL hC hrows hclear ha haℓ
  refine ⟨β, hβ, ?_⟩
  intro r pre hpre hne
  have hint := (hresult r pre hpre hne).2
  refine ⟨hint 0 1 (le_refl 0) zero_le_one (le_refl 1), ?_⟩
  intro p₀ hp₀
  simpa only [sub_self] using hint p₀ p₀ hp₀.1 (le_refl p₀) hp₀.2

end TNLeanTest.ActualTransportEstimates
