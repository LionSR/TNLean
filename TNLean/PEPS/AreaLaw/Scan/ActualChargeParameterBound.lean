/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualParameterIntegral
import TNLean.PEPS.AreaLaw.Scan.ActualTransportEstimates

/-!
# Integrated charge defect for one actual round

The good-history sampling inequality and the integrated entropy estimate give
a bound for the literal scalar charge defect on every closed subinterval of
`[0, 1]`. Both scalar functions are interval integrable: the charge defect by
the old-state integral theorem, and the entropy gain by the transport-state
expectation theorem. Neither function is assumed continuous in the parameter.

The logarithmic error is uniform in the replica count and the supplied nonzero
symmetric vector. Zero replicas and equal interval endpoints are included.
No common physical pre-vector or compatibility between successive rounds is
asserted.

This is the one-round consequence of the actual charge sampling inequality and
Proposition 7.4 of OpenAI, *A two-dimensional area law from a global spectral
gap*, `06-transport.tex`, lines 377–434, at `openai/math@adc7f124`.
-/

open scoped BigOperators
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open TensorPower TensorPower.ReplicaTransport

private theorem mul_integral_le_of_integral_sub_le
    {Q G : ℝ → ℝ} {p₀ p₁ c α A B L : ℝ} (hc : 0 ≤ c) (h01 : p₀ ≤ p₁)
    (hQ : IntervalIntegrable Q volume p₀ p₁)
    (hG : IntervalIntegrable G volume p₀ p₁)
    (hcompare : ∀ p ∈ Icc p₀ p₁, α * Q p ≤ G p)
    (htransport : (∫ p in p₀..p₁, c * G p - A - B) ≤ L) :
    c * α * (∫ p in p₀..p₁, Q p) ≤ L + (p₁ - p₀) * (A + B) := by
  have hmono : c * α * (∫ p in p₀..p₁, Q p) ≤ c * (∫ p in p₀..p₁, G p) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on h01 (hQ.const_mul _) (hG.const_mul _) ?_
    intro p hp
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcompare p hp) hc
  rw [intervalIntegral.integral_sub ((hG.const_mul c).sub intervalIntegrable_const)
      intervalIntegrable_const,
    intervalIntegral.integral_sub (hG.const_mul c) intervalIntegrable_const,
    intervalIntegral.integral_const_mul] at htransport
  simp only [intervalIntegral.integral_const, smul_eq_mul] at htransport
  linarith

/-- On an ordered subinterval of `[0, 1]`, the actual charge defect satisfies
the integrated entropy estimate with coefficient
`r * a / (2 * (C₁ + 1) * n * D)`. The error is multiplied by the interval length.
The constants precede all geometric and Hamiltonian choices, and the logarithmic
error sequence precedes the replica count and nonzero symmetric vector. -/
theorem actualCharge_integral_bound_domainGraph :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x => ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {s L μ : ℕ} (hn : 2 ≤ S.n), s + 1 ≤ S.n * S.m → 2 * S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hCpos : 0 < S.C₁), 3 * (μ : ℝ) ≤ S.C₁ →
        (∀ d : ℕ, 1 ≤ d → d ≤ L →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ x, (Finset.univ.filter fun i => S.anchor i = x).card ≤ μ) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hCpos (by omega) hDpos
        let n := augmentedDimensions (V := Site Λ) q aux
        let D := S.actualChargeData hm hM s
        let E := S.actualEnergyTerms h Ω Δ L aux
        let ℓ := transportLogDimBound q S.r₀
        ∃ β : ℕ → ℝ, (β =O[atTop] fun r : ℕ => Real.log (r + 1)) ∧
          ∀ (r : ℕ) (pre : Config r (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace r (fun v => Fin (n v)) → pre ≠ 0 →
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              (r : ℝ) * a * ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)) *
                  (∫ p in p₀..p₁, S.actualChargeEntropyDefect hm hM s n E (a / 2) r pre p) ≤
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₀) pre) -
                  Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) r p₁) pre) +
                  (p₁ - p₀) *
                    (Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β r) := by
  classical
  obtain ⟨c₀, Cent, eent, _, _, hc₀, htransport⟩ := actualCharge_transport_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    s L μ hn hs hr hDpos hD hL hCpos hC hrows hmult hclear a ha haℓ
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hCpos (by omega) hDpos
  let n := augmentedDimensions (V := Site Λ) q aux
  let D := S.actualChargeData hm hM s
  let E := S.actualEnergyTerms h Ω Δ L aux
  have hn0 : 0 < S.n := by omega
  have hr' : S.r₀ ≤ S.D := by omega
  obtain ⟨β, _, hβ, _, hresult⟩ := htransport aux h Ω S hT hgraph hdepth hanchor hΔ hΩ
    hn0 hs hr' hDpos hD hL hCpos hrows hclear ha haℓ
  refine ⟨β, hβ, ?_⟩
  intro r pre hpre hne p₀ p₁ h0 h01 h1
  have ht : 0 ≤ a / 2 := (half_pos ha).le
  have hsub : Set.uIcc p₀ p₁ ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le h01, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc h0 h1
  have hQ := (S.intervalIntegrable_actualChargeEntropyDefect hm hM s n E ht r pre).mono_set hsub
  have hG := (D.intervalIntegrable_entropyGain (S.actualChargeData_isAdmissible hm hM s)
    ht (S.chargeTransportData_crossBandCommute _ _ n ht r) hne).mono_set hsub
  apply mul_integral_le_of_integral_sub_le (mul_nonneg (Nat.cast_nonneg r) ha.le) h01 hQ hG
  · intro p _
    exact S.actualChargeEntropyDefect_le_entropyGain_domainGraph hT hgraph hdepth hm hM
      n E (fun _ => rfl) hn (by omega) hs hr hD hDpos hL hC hrows hmult hclear ht r pre p
  · exact (hresult r pre hpre hne).2 p₀ p₁ h0 h01 h1

end TNLean.PEPS.AreaLaw.Scan.CollarScan
