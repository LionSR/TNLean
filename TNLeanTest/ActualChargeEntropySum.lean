/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEntropySum

/-!
# Endpoints and zero replicas in the summed charge bound

Equal endpoints and zero replicas annihilate the retained charge contribution.
The full-round error is not multiplied by the retained interval length. The
entropy sign includes the zero vector, while gain integrability retains its
nonzero-vector hypothesis even at zero replicas.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix TensorPower TensorPower.ReplicaTransport MeasureTheory PermutationRepresentation Entropy
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan

noncomputable section

namespace TNLeanTest.ActualChargeEntropySum

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)

/-- The retained sum vanishes on a zero-length interval, with no sign
restriction on either scalar coefficient. -/
theorem equal_endpoints_charge_sum (c α t p : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) :
    c * α * (∑ s : Fin (S.n * S.m),
      ∫ x in p..p, S.actualChargeEntropyDefect hm hM s.val n E t k pre x) = 0 := by
  simp

/-- Zero replicas give a zero prefactor on every subinterval. The supplied
vector is unrestricted; no division by the replica count is used. -/
theorem zero_replica_charge_sum (a α t p₀ p₁ : ℝ)
    (pre : Config 0 (fun v => Fin (n v)) → ℂ) :
    (0 : ℝ) * a * α * (∑ s : Fin (S.n * S.m),
      ∫ p in p₀..p₁, S.actualChargeEntropyDefect hm hM s.val n E t 0 pre p) = 0 := by
  simp

/-- The fill sign holds for the zero supplied vector and at every real
parameter, without symmetry or an interior-parameter assumption. -/
theorem fill_gain_nonneg_zero_pre (s k : ℕ) {t : ℝ} (ht : 0 ≤ t) (p : ℝ) :
    0 ≤ (S.actualFillData hm hM s).entropyGain n t k 0 p :=
  (S.actualFillData hm hM s).entropyGain_nonneg n
    (S.actualFillData_isAdmissible hm hM s) ht
    (S.fillTransportData_crossBandCommute _ n ht k) 0 p

/-- Every actual round retains its integrability statement at zero replicas
for the same nonzero supplied vector. No symmetry assumption is needed here. -/
theorem zero_replica_round_integrability {t : ℝ} (ht : 0 ≤ t)
    (pre : Config 0 (fun v => Fin (n v)) → ℂ) (hne : pre ≠ 0)
    (j : Fin (2 * S.n * S.m)) :
    IntervalIntegrable ((S.actualRoundData hm hM j).entropyGain n t 0 pre) volume 0 1 :=
  (S.actualRoundData hm hM j).intervalIntegrable_entropyGain
    (S.actualRoundData_isAdmissible hm hM j) ht
    (S.actualRoundData_crossBandCommute hm hM j n ht 0) hne

/-- The full charge bound chooses one logarithmic error before every replica
count, supplied vector and retained closed interval. -/
omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
theorem capstone_signature :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {L μ : ℕ} (hn : 2 ≤ S.n), 2 * S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hCpos : 0 < S.C₁), 3 * (μ : ℝ) ≤ S.C₁ →
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ x, (Finset.univ.filter fun i => S.anchor i = x).card ≤ μ) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hCpos (Nat.le_trans (by decide) hn) hDpos
        let n := augmentedDimensions (V := Site Λ) q aux
        let E := S.actualEnergyTerms h Ω Δ L aux
        let ℓ := transportLogDimBound q S.r₀
        ∃ (β : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧
          (∀ k, 0 ≤ β k) ∧ (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              (k : ℝ) * a * ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)) *
                  (∑ s : Fin (S.n * S.m),
                    ∫ p in p₀..p₁,
                      S.actualChargeEntropyDefect hm hM s.val n E (a / 2) k pre p) ≤
                Real.log (Transport.filteredNormSq
                  ((S.actualFillData hm hM 0).rootPath n (a / 2) k 0) pre) -
                  Real.log (Transport.filteredNormSq
                    ((S.actualFillData hm hM (S.n * S.m)).rootPath n (a / 2) k 0) pre) +
                  (2 * S.n * S.m : ℕ) *
                    (Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β k) :=
  CollarScan.actualCharges_integral_bound_domainGraph

/-- Equal endpoints retain all complete-round errors. In particular, the
right side still contains exactly `2 * S.n * S.m` copies of the same error. -/
omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
theorem equal_endpoints_full_error :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (_h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {L μ : ℕ} (hn : 2 ≤ S.n), 2 * S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hCpos : 0 < S.C₁), 3 * (μ : ℝ) ≤ S.C₁ →
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ x, (Finset.univ.filter fun i => S.anchor i = x).card ≤ μ) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hCpos (Nat.le_trans (by decide) hn) hDpos
        let n := augmentedDimensions (V := Site Λ) q aux
        let ℓ := transportLogDimBound q S.r₀
        ∃ (β : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧
          (∀ k, 0 ≤ β k) ∧ (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
            ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
              0 ≤
                Real.log (Transport.filteredNormSq
                  ((S.actualFillData hm hM 0).rootPath n (a / 2) k 0) pre) -
                  Real.log (Transport.filteredNormSq
                    ((S.actualFillData hm hM (S.n * S.m)).rootPath n (a / 2) k 0) pre) +
                  (2 * S.n * S.m : ℕ) *
                    (Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β k) := by
  obtain ⟨c₀, Cent, eent, hc₀, hbound⟩ := CollarScan.actualCharges_integral_bound_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    L μ hn hr hDpos hD hL hCpos hC hrows hmult hclear a ha haℓ
  obtain ⟨β, Cβ, hCβ, hβ0, hβ, hcharge⟩ :=
    hbound aux h Ω S hT hgraph hdepth hanchor hΔ hΩ hn hr hDpos hD hL hCpos hC
      hrows hmult hclear ha haℓ
  refine ⟨β, Cβ, hCβ, hβ0, hβ, ?_⟩
  intro k pre hpre hne p h0 h1
  simpa only [intervalIntegral.integral_same, Finset.sum_const_zero, mul_zero] using
    hcharge k pre hpre hne p p h0 le_rfl h1

end TNLeanTest.ActualChargeEntropySum
