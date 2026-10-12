/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualParameterIntegral
import TNLean.PEPS.AreaLaw.Scan.ActualRoundEntropy

/-!
# Charge entropy summed over the actual scan

Every admissible move has nonnegative conditional mutual information. Its old-state
Fourier-coherent integral is therefore nonnegative, including during a fill. The
geometric charge-sampling inequality can first be integrated on any closed
subinterval of `[0, 1]`, then compared with the full-round entropy integral.

The charge stages inject into the odd rounds. Adding the nonnegative fill gains and
applying the actual finite-round telescope leaves the initial and final logarithmic
norms, with the common error paid exactly `2 * S.n * S.m` times. One error function
is chosen before every replica count, supplied vector and subinterval. Identification
with the physical prevector and initial and terminal norm comparisons remain separate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 321–330, and `08-scanner.tex`, lines 442–479,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently
formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport.TransportData

variable {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
variable {H : Type*} [Fintype H] [DecidableEq H]
variable {C : H → Type*} [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)]

/-- Strong subadditivity makes every move symbol nonnegative; positive history
weights and the old-state integrals preserve this sign. The supplied vector may
vanish, and the interpolation parameter may be either endpoint. -/
theorem entropyGain_nonneg (D : TransportData V K H C)
    (n : V → ℕ) [∀ v, NeZero (n v)] (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    0 ≤ D.entropyGain n t k pre p := by
  rw [D.entropyGain_eq_sum_oldFourierCoherentIntegral n t k pre p]
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (hD.histWeight_pos h).le
    (D.oldFourierCoherentIntegral_nonneg n hD ht hcomm pre p h
      (D.continuous_choiceEntropySymbol n h) (D.choiceEntropySymbol_nonneg n hD h))

end TensorPower.ReplicaTransport.TransportData

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open TensorPower TensorPower.ReplicaTransport

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- The sum of actual charge defects on a closed subinterval is dominated by
the entropy integrated over all complete rounds. The proof inserts each charge
stage at its odd round and derives the nonnegativity of the remaining fill gains.
Only interval integrability, not continuity in the parameter, is used. -/
theorem sum_actualCharge_integral_le_sum_actualRounds_entropyGain_domainGraph
    {Λ T : Finset (ℤ × ℤ)} (hT : T.Nonempty)
    (S : CollarScan (Site Λ) I) (hgraph : S.graph = domainGraph Λ)
    (hdepth : S.depth = fun x => ambientDepth T hT x.val) {L μ : ℕ}
    (hm0 : 0 < S.m) (hM : 0 < S.M)
    (n : Site Λ ⊕ Bool → ℕ) [∀ v, NeZero (n v)]
    (E : EnergyTerms (Site Λ ⊕ Bool) n I)
    (hsupport : ∀ i, E.support i =
      (designatedSupport S.graph (S.truncationSet L) S.r₀ (S.anchor i)).map
        ⟨Sum.inl, Sum.inl_injective⟩)
    (hn : 2 ≤ S.n) (hm : 2 ≤ S.m) (hr : 2 * S.r₀ ≤ S.D)
    (hD : 4 * S.D ≤ S.m) (hDpos : 1 ≤ S.D)
    (hL : 8 * S.K * S.m ≤ L) (hC : 3 * (μ : ℝ) ≤ S.C₁)
    (hrows : ∀ d : ℕ, 1 ≤ d → d ≤ L →
      (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n)
    (hmult : ∀ x, (Finset.univ.filter fun i => S.anchor i = x).card ≤ μ)
    (hclear : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
      ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z)
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (hne : pre ≠ 0)
    {p₀ p₁ : ℝ} (h0 : 0 ≤ p₀) (h01 : p₀ ≤ p₁) (h1 : p₁ ≤ 1) :
    ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)) *
        (∑ s : Fin (S.n * S.m),
          ∫ p in p₀..p₁, S.actualChargeEntropyDefect hm0 hM s.val n E t k pre p) ≤
      ∑ j : Fin (2 * S.n * S.m),
        ∫ p in (0 : ℝ)..1, (S.actualRoundData hm0 hM j).entropyGain n t k pre p := by
  classical
  let α : ℝ := (1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D)
  let e (s : Fin (S.n * S.m)) : Fin (2 * S.n * S.m) :=
    ⟨2 * s.val + 1, by rw [Nat.mul_assoc]; have hs := s.isLt; omega⟩
  have hinj : Function.Injective e := by
    intro s s' h
    apply Fin.ext
    have hval := congrArg Fin.val h
    dsimp only [e] at hval
    omega
  have hsub : Set.uIcc p₀ p₁ ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le h01, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc h0 h1
  have hG0 (j : Fin (2 * S.n * S.m)) (p : ℝ) :
      0 ≤ (S.actualRoundData hm0 hM j).entropyGain n t k pre p :=
    (S.actualRoundData hm0 hM j).entropyGain_nonneg n
      (S.actualRoundData_isAdmissible hm0 hM j) ht
      (S.actualRoundData_crossBandCommute hm0 hM j n ht k) pre p
  have hGint (j : Fin (2 * S.n * S.m)) :
      IntervalIntegrable ((S.actualRoundData hm0 hM j).entropyGain n t k pre) volume 0 1 :=
    (S.actualRoundData hm0 hM j).intervalIntegrable_entropyGain
      (S.actualRoundData_isAdmissible hm0 hM j) ht
      (S.actualRoundData_crossBandCommute hm0 hM j n ht k) hne
  have hstep (s : Fin (S.n * S.m)) :
      α * (∫ p in p₀..p₁, S.actualChargeEntropyDefect hm0 hM s.val n E t k pre p) ≤
        ∫ p in (0 : ℝ)..1, (S.actualRoundData hm0 hM (e s)).entropyGain n t k pre p := by
    have hodd : IsChargeRound (e s).val := by
      change (2 * s.val + 1) % 2 = 1
      omega
    have hstage : (e s).val / 2 = s.val := by dsimp only [e]; omega
    have heq (p : ℝ) : (S.actualRoundData hm0 hM (e s)).entropyGain n t k pre p =
        (S.actualChargeData hm0 hM s.val).entropyGain n t k pre p := by
      refine S.actualRoundData_induction hm0 hM (e s)
        (fun _ _ _ D => D.entropyGain n t k pre p =
          (S.actualChargeData hm0 hM s.val).entropyGain n t k pre p) ?_ ?_
      · intro _
        exact congrArg (fun stage =>
          (S.actualChargeData hm0 hM stage).entropyGain n t k pre p) hstage
      · intro hfill
        exact (hfill hodd).elim
    have hQ := (S.intervalIntegrable_actualChargeEntropyDefect hm0 hM s.val n E ht k pre).mono_set
      hsub
    calc
      α * (∫ p in p₀..p₁, S.actualChargeEntropyDefect hm0 hM s.val n E t k pre p) =
          ∫ p in p₀..p₁, α * S.actualChargeEntropyDefect hm0 hM s.val n E t k pre p :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ p in p₀..p₁, (S.actualRoundData hm0 hM (e s)).entropyGain n t k pre p := by
        apply intervalIntegral.integral_mono_on h01 (hQ.const_mul α) ((hGint (e s)).mono_set hsub)
        intro p _
        rw [heq]
        exact S.actualChargeEntropyDefect_le_entropyGain_domainGraph hT hgraph hdepth hm0 hM
          n E hsupport hn hm (Nat.succ_le_iff.mpr s.isLt) hr hD hDpos hL hC hrows hmult
          hclear ht k pre p
      _ ≤ ∫ p in (0 : ℝ)..1, (S.actualRoundData hm0 hM (e s)).entropyGain n t k pre p :=
        intervalIntegral.integral_mono_interval h0 h01 h1
          (Filter.Eventually.of_forall (hG0 (e s))) (hGint (e s))
  change α * _ ≤ _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum_of_injOn e hinj.injOn (Finset.subset_univ _)
    (fun s _ => hstep s) (fun j _ _ =>
      intervalIntegral.integral_nonneg_of_forall zero_le_one (hG0 j))

/-- Actual charge sampling and the common-error telescope bound all charge
stages on any closed subinterval of `[0, 1]` (`08-scanner.tex`, lines 442–479).
The error is paid for every complete fill and charge round, independently of
the retained subinterval's length. The same logarithmic error works for all
replica counts and all nonzero symmetric supplied vectors. -/
theorem actualCharges_integral_bound_domainGraph :
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
                    (Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β k) := by
  classical
  obtain ⟨c₀, Cent, eent, hc₀, hbound⟩ := actualRounds_entropy_integral_le_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    L μ hn hr hDpos hD hL hCpos hC hrows hmult hclear a ha haℓ
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hCpos (Nat.le_trans (by decide) hn) hDpos
  let n := augmentedDimensions (V := Site Λ) q aux
  let E := S.actualEnergyTerms h Ω Δ L aux
  obtain ⟨β, Cβ, hCβ, hβ0, hβ, hround⟩ :=
    hbound aux h Ω S hT hgraph hdepth hanchor hΔ hΩ (by omega) (by omega) hDpos hD hL
      hCpos hrows hclear ha haℓ
  refine ⟨β, Cβ, hCβ, hβ0, hβ, ?_⟩
  intro k pre hpre hne p₀ p₁ h0 h01 h1
  have hcharge := S.sum_actualCharge_integral_le_sum_actualRounds_entropyGain_domainGraph
    hT hgraph hdepth hm hM n E (fun _ => rfl) hn (by omega) hr hD hDpos hL hC
    hrows hmult hclear (half_pos ha).le k pre hne h0 h01 h1
  have hscaled := mul_le_mul_of_nonneg_left hcharge (mul_nonneg (Nat.cast_nonneg k) ha.le)
  rw [← mul_assoc] at hscaled
  exact hscaled.trans (hround k pre hpre hne)

end TNLean.PEPS.AreaLaw.Scan.CollarScan
