/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoundEntropy

/-!
# Actual-round entropy summation regressions

Exact signatures preserve all geometric hypotheses and the order of the common
constants and error. The successive root identities and scalar telescope include zero copies;
an empty family leaves the same initial and final root. No energy hypothesis appears.
-/

set_option autoImplicit false

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open TensorPower TensorPower.ReplicaTransport

noncomputable section
namespace TNLeanTest.ActualRoundEntropy

-- Exact source-facing statement: one error before every replica count and vector.
example :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (_h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {L : ℕ} (hn : 0 < S.n), S.r₀ ≤ S.D →
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
        let D := S.actualRoundData hm hM
        let ℓ := transportLogDimBound q S.r₀
        ∃ (β : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧
          (∀ k, 0 ≤ β k) ∧ (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
            (k : ℝ) * a * ∑ j : Fin (2 * S.n * S.m),
                ∫ p in (0 : ℝ)..1, (D j).entropyGain n (a / 2) k pre p ≤
              Real.log (Transport.filteredNormSq
                ((S.actualFillData hm hM 0).rootPath n (a / 2) k 0) pre) -
                Real.log (Transport.filteredNormSq
                  ((S.actualFillData hm hM (S.n * S.m)).rootPath n (a / 2) k 0) pre) +
                (2 * S.n * S.m : ℕ) *
                  (Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β k) :=
  CollarScan.actualRounds_entropy_integral_le_domainGraph

-- The zero-copy consequence needs no physical energy or positive-copy premise.
example :
    ∃ c₀ _Cent _eent : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (_h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {L : ℕ} (hn : 0 < S.n), S.r₀ ≤ S.D →
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
        let _D := S.actualRoundData hm hM
        let _ℓ := transportLogDimBound q S.r₀
        ∃ (β : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧
          (∀ k, 0 ≤ β k) ∧ (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧
          ∀ (pre : Config 0 (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace 0 (fun v => Fin (n v)) → pre ≠ 0 →
            0 ≤
              Real.log (Transport.filteredNormSq
                ((S.actualFillData hm hM 0).rootPath n (a / 2) 0 0) pre) -
                Real.log (Transport.filteredNormSq
                  ((S.actualFillData hm hM (S.n * S.m)).rootPath n (a / 2) 0 0) pre) +
                (2 * S.n * S.m : ℕ) * β 0 := by
  obtain ⟨c₀, Cent, eent, hc₀, htransport⟩ :=
    CollarScan.actualRounds_entropy_integral_le_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    L hn hr hDpos hD hL hC hrows hclear a ha haℓ
  obtain ⟨β, Cβ, hCβ, hβ0, hβ, hresult⟩ :=
    htransport aux h Ω S hT hgraph hdepth hanchor hΔ hΩ hn hr hDpos hD hL hC
      hrows hclear ha haℓ
  refine ⟨β, Cβ, hCβ, hβ0, hβ, ?_⟩
  intro pre hpre hne
  simpa only [Nat.cast_zero, mul_zero, zero_mul, zero_add] using hresult 0 pre hpre hne

section Roots

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
variable (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t)

-- Both parity cases are proved for every index, not just for a first pair.
example (j : Fin (2 * S.n * S.m)) (hj : j.val + 1 < 2 * S.n * S.m) (k : ℕ) :
    (S.actualRoundData hm hM j).rootPath n t k 1 =
      (S.actualRoundData hm hM ⟨j.val + 1, hj⟩).rootPath n t k 0 :=
  S.actualRoundData_rootPath_one_eq_succ_zero hm hM j hj n ht k

example (j : Fin (2 * S.n * S.m)) (hj : j.val + 1 < 2 * S.n * S.m) :
    (S.actualRoundData hm hM j).rootPath n t 0 1 =
      (S.actualRoundData hm hM ⟨j.val + 1, hj⟩).rootPath n t 0 0 :=
  S.actualRoundData_rootPath_one_eq_succ_zero hm hM j hj n ht 0

-- The telescope retains the computed terminal history length and the correct sign.
example (hnm : 0 < S.n * S.m) (k : ℕ) :
    let j : Fin (2 * S.n * S.m) :=
      ⟨2 * S.n * S.m - 1, by rw [Nat.mul_assoc]; omega⟩
    (S.actualRoundData hm hM j).rootPath n t k 1 =
      (S.actualFillData hm hM (S.n * S.m)).rootPath n t k 0 := by
  dsimp only
  apply S.actualRoundData_rootPath_one_of_last hm hM _ _ n ht k
  simp only
  rw [Nat.mul_assoc]
  omega

example (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ) :
    ∑ j : Fin (2 * S.n * S.m),
        (Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t k 0) pre) -
          Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t k 1) pre)) =
      Real.log (Transport.filteredNormSq ((S.actualFillData hm hM 0).rootPath n t k 0) pre) -
        Real.log (Transport.filteredNormSq
          ((S.actualFillData hm hM (S.n * S.m)).rootPath n t k 0) pre) :=
  S.sum_actualRoundData_logNormSq_sub hm hM n ht k pre

example (pre : Config 0 (fun v => Fin (n v)) → ℂ) :
    ∑ j : Fin (2 * S.n * S.m),
        (Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t 0 0) pre) -
          Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t 0 1) pre)) =
      Real.log (Transport.filteredNormSq ((S.actualFillData hm hM 0).rootPath n t 0 0) pre) -
        Real.log (Transport.filteredNormSq
          ((S.actualFillData hm hM (S.n * S.m)).rootPath n t 0 0) pre) :=
  S.sum_actualRoundData_logNormSq_sub hm hM n ht 0 pre

-- Empty round families do not require an artificial first or last Fin index.
example (hn : S.n = 0) (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ) :
    ∑ j : Fin (2 * S.n * S.m),
        (Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t k 0) pre) -
          Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t k 1) pre)) =
      0 := by
  rw [S.sum_actualRoundData_logNormSq_sub hm hM n ht k pre]
  simp only [hn, Nat.zero_mul, sub_self]

-- The exact algebraic identity also applies to the zero vector.
example (k : ℕ) :
    ∑ j : Fin (2 * S.n * S.m),
        (Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t k 0) 0) -
          Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t k 1) 0)) =
      Real.log (Transport.filteredNormSq ((S.actualFillData hm hM 0).rootPath n t k 0) 0) -
        Real.log (Transport.filteredNormSq
          ((S.actualFillData hm hM (S.n * S.m)).rootPath n t k 0) 0) :=
  S.sum_actualRoundData_logNormSq_sub hm hM n ht k 0

example (j : Fin (2 * S.n * S.m)) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (hne : pre ≠ 0) :
    IntervalIntegrable ((S.actualRoundData hm hM j).entropyGain n t k pre) volume 0 1 :=
  (S.actualRoundData hm hM j).intervalIntegrable_entropyGain
    (S.actualRoundData_isAdmissible hm hM j) ht
    (S.actualRoundData_crossBandCommute hm hM j n ht k) hne

end Roots
end TNLeanTest.ActualRoundEntropy
