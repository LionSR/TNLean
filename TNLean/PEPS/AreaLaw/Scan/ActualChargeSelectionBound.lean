/-
Copyright (c) 2026 Sirui Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeEntropySum
import TNLean.PEPS.AreaLaw.Scan.ActualChargeSelection

/-!
# Selection from the integrated actual charge estimate

The integrated estimate for the scheduled charge stages selects one stage and
one common interpolation parameter for the same supplied vector. The universal
constants precede the physical data. For each choice of these data, one
logarithmic error sequence applies to every replica count, supplied symmetric
vector and interpolation interval. Both endpoint transport roots are retained.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`08-scanner.tex`, lines 442–490.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open scoped BigOperators
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy
open TensorPower TensorPower.ReplicaTransport

/-- The established all-charge integral bound selects a literal actual charge
stage and a common parameter on every nondegenerate subinterval of `[0,1]`.
The constants precede the physical data, and one logarithmic error sequence
precedes every replica count, supplied nonzero symmetric vector and interval.
The initial and final filtered norms retain the original roots and vector.
Source: area-law manuscript, `08-scanner.tex`, lines 442–490.
This is the finite averaging consequence; the physical endpoint estimates of
Proposition 9.2 are not asserted here. -/
theorem actualCharges_selection_domainGraph :
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
            0 < k → pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ < p₁ → p₁ ≤ 1 →
              let ρ := (k : ℝ) * a *
                ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D))
              let B := Real.log (Transport.filteredNormSq
                ((S.actualFillData hm hM 0).rootPath n (a / 2) k 0) pre) -
                Real.log (Transport.filteredNormSq
                  ((S.actualFillData hm hM (S.n * S.m)).rootPath n (a / 2) k 0) pre) +
                (2 * S.n * S.m : ℕ) *
                  (Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β k)
              ∃ s : Fin (S.n * S.m), ∃ p ∈ Icc p₀ p₁,
                S.actualChargeEntropyDefect hm hM s.val n E (a / 2) k pre p ≤
                  B / (ρ * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀)) := by
  obtain ⟨c₀, Cent, eent, hc₀, hbound⟩ := actualCharges_integral_bound_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    L μ hn hr hDpos hD hL hCpos hC hrows hmult hclear a ha haℓ hm hM n E ℓ
  obtain ⟨β, Cβ, hCβ, hβ0, hβ, hsum⟩ :=
    hbound aux h Ω S hT hgraph hdepth hanchor hΔ hΩ hn hr hDpos hD hL hCpos hC
      hrows hmult hclear ha haℓ
  refine ⟨β, Cβ, hCβ, hβ0, hβ, fun k pre hk hpre hne p₀ p₁ h0 h01 h1 ↦ ?_⟩
  exact S.exists_actualCharge_point_of_sum_integral_le hm hM (by omega) n E ha.le k pre
    h0 h01 h1
    (mul_pos (mul_pos (Nat.cast_pos.mpr hk) ha)
      (div_pos (one_div_pos.mpr (mul_pos zero_lt_two (add_pos hCpos zero_lt_one)))
        (mul_pos (Nat.cast_pos.mpr (show 0 < S.n by omega)) (Nat.cast_pos.mpr hDpos))))
    (hsum k pre hpre hne p₀ p₁ h0 h01.le h1)

end TNLean.PEPS.AreaLaw.Scan.CollarScan
