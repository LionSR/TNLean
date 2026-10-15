/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualChargeSelectionBound
import TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport
import TNLean.PEPS.AreaLaw.Scan.ActualGlobalReplicaEnergy

/-!
# Energy at the selected actual charge point

The accepted actual charge selection and uniform finite-family transport
estimate use the same supplied prevector. Selection retains its literal
endpoint log-norm bound; the energy conclusion concerns that selected stage
and that same common interpolation parameter. One vanishing error precedes
all replica counts, selected stages, vectors and parameters.

The excess energy is divided by the source truncated gap `g / 2`.
The surviving ground-energy contribution is `e₀`, since transport bounds
the mean energy by `2 * e₀` plus its error. No zero ground energy, physical
prevector construction, selected density power or final-scale decay is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 442--533 and 839--865, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix Set Filter Topology MeasureTheory PermutationRepresentation
open TensorPower TensorPower.ReplicaTransport
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

open Classical in
/-- Select one literal charge and retain its actual energy bound. The input
eigenvalue equation is for the actual augmented truncated replica Hamiltonian.
For the physical application it is the equation of the already selected
Schmidt--Bell prevector of the same target-window ground vector.

The source gap normalization is explicit. This theorem does not construct
the physical gap or replace the endpoint log norms by comparator budgets.
Source: `08-scanner.tex`, lines 480--533. -/
theorem actualCharges_selection_energy_domainGraph :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q d R : ℕ} {J Δ : ℝ}
        [NeZero q] [NeZero d] [LinearOrder (AdmissibleSupport Λ R)]
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hT : T.Nonempty),
        S.graph = domainGraph Λ →
        S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        ∀ {L multiplicity : ℕ} (hn : 2 ≤ S.n), 2 * S.r₀ ≤ S.D →
        ∀ (hDpos : 1 ≤ S.D) (hD : 4 * S.D ≤ S.m),
        8 * S.K * S.m ≤ L → ∀ (hCpos : 0 < S.C₁),
        3 * (multiplicity : ℝ) ≤ S.C₁ →
        (∀ r : ℕ, 1 ≤ r → r ≤ L →
          (ambientDilation T r \ ambientDilation T (r - 1)).card ≤ S.n) →
        (∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ multiplicity) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * L + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ {a : ℝ}, 0 < a → a * transportLogDimBound q S.r₀ ≤ c₀ →
        let hm : 0 < S.m := by omega
        let hM : 0 < S.M := chargeSlotCount_pos hCpos (Nat.le_trans (by decide) hn) hDpos
        let dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
        let E := S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)
        let ℓ := transportLogDimBound q S.r₀
        let g := Δ / positiveNormalization 1 (Δ / 2) J
        let Hbar := fun k ↦ copyMean dims k
          (augmentOperator q (fun _ ↦ d) (∑ i, S.truncatedEnergyTerm h Ω Δ L i))
        ∃ (β rem : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧
          (∀ k, 0 ≤ β k) ∧ (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧
          (∀ k, 0 ≤ rem k) ∧ Tendsto rem atTop (𝓝 0) ∧
          ∀ (pre : (k : ℕ) → Config k (fun v ↦ Fin (dims v)) → ℂ)
            (k : ℕ), 0 < k →
            pre k ∈ symmetricSubspace k (fun v ↦ Fin (dims v)) → pre k ≠ 0 →
            ∀ e₀ : ℝ, Hbar k *ᵥ pre k = (e₀ : ℂ) • pre k →
            ∀ p₀ p₁ : ℝ, 0 < p₀ → p₀ < p₁ → p₁ < 1 →
              let ρ := (k : ℝ) * a *
                ((1 / (2 * (S.C₁ + 1))) / ((S.n : ℝ) * S.D))
              let B := Real.log (Transport.filteredNormSq
                ((S.actualFillData hm hM 0).rootPath dims (a / 2) k 0) (pre k)) -
                Real.log (Transport.filteredNormSq
                  ((S.actualFillData hm hM (S.n * S.m)).rootPath dims (a / 2) k 0)
                    (pre k)) +
                (2 * S.n * S.m : ℕ) *
                  (Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β k)
              ∃ s : Fin (S.n * S.m), ∃ p ∈ Icc p₀ p₁,
                S.actualChargeEntropyDefect hm hM s.val dims E (a / 2) k (pre k) p ≤
                  B / (ρ * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀)) ∧
                ((S.actualChargeScanRound hm hM s.val dims E a pre).meanEnergy k p - e₀) /
                    (g / 2) ≤
                  (e₀ + Cen * a ^ 2 * ℓ ^ een *
                    (S.actualChargeData hm hM s.val).energyError E (a / 2) k (pre k) p +
                    rem k) / (g / 2) := by
  classical
  obtain ⟨cs, Cent, eent, hcs, hselection⟩ := actualCharges_selection_domainGraph
  obtain ⟨ct, _, _, Cen, een, hct, htransport⟩ := actualRounds_transport_domainGraph
  refine ⟨min cs ct, Cent, eent, Cen, een, lt_min hcs hct, ?_⟩
  intro Λ T q d R J Δ _ _ _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    L multiplicity hn hr hDpos hD hL hCpos hC hrows hmult hclear a ha hasmall
    hm hM dims E ℓ g Hbar
  have hsmallS : a * transportLogDimBound q S.r₀ ≤ cs :=
    hasmall.trans (min_le_left _ _)
  have hsmallT : a * transportLogDimBound q S.r₀ ≤ ct :=
    hasmall.trans (min_le_right _ _)
  obtain ⟨β, Cβ, hCβ, hβ0, hβ, hselected⟩ :=
    hselection (fun _ ↦ d) h Ω S hT hgraph hdepth hanchor hΔ hΩ
      hn hr hDpos hD hL hCpos hC hrows hmult hclear ha hsmallS
  obtain ⟨_, rem, _, _, _, hrem0, _, hrem, hround⟩ :=
    htransport (fun _ ↦ d) h Ω S hT hgraph hdepth hanchor hΔ hΩ
      (show 0 < S.n by omega) (show S.r₀ ≤ S.D by omega) hDpos hD hL
      hCpos hrows hclear ha hsmallT
  refine ⟨β, rem, Cβ, hCβ, hβ0, hβ, hrem0, hrem, ?_⟩
  intro pre k hk hsym hpre e₀ heigen p₀ p₁ hp₀ hp₀₁ hp₁ ρ B
  obtain ⟨s, p, hp, hQ⟩ := hselected k (pre k) hk hsym hpre
    p₀ p₁ hp₀.le hp₀₁ hp₁.le
  have hpInterior : p ∈ Ioo (0 : ℝ) 1 :=
    ⟨hp₀.trans_le hp.1, hp.2.trans_lt hp₁⟩
  let j : Fin (2 * S.n * S.m) := ⟨2 * s.val + 1, by
    rw [Nat.mul_assoc]
    have := s.isLt
    omega⟩
  have hj : IsChargeRound j.val := by
    dsimp only [j, IsChargeRound]
    omega
  have hjhalf : j.val / 2 = s.val := by dsimp only [j]; omega
  have hbridge :
      (S.actualRoundData hm hM j).rootPath dims (a / 2) k p =
        (S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p ∧
      (S.actualRoundData hm hM j).energyError E (a / 2) k (pre k) p =
        (S.actualChargeData hm hM s.val).energyError E (a / 2) k (pre k) p := by
    refine S.actualRoundData_induction hm hM j
      (fun _ _ _ D ↦
        D.rootPath dims (a / 2) k p =
          (S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p ∧
        D.energyError E (a / 2) k (pre k) p =
          (S.actualChargeData hm hM s.val).energyError E (a / 2) k (pre k) p) ?_ ?_
    · intro _
      exact ⟨congrArg (fun t : ℕ ↦
        (S.actualChargeData hm hM t).rootPath dims (a / 2) k p) hjhalf,
        congrArg (fun t : ℕ ↦
          (S.actualChargeData hm hM t).energyError E (a / 2) k (pre k) p) hjhalf⟩
    · intro hnot
      exact (hnot hj).elim
  have henergy := ((hround j k (pre k) hsym hpre).1 p hpInterior).2.2 e₀ heigen
  have hmean : (S.actualChargeScanRound hm hM s.val dims E a pre).meanEnergy k p ≤
      2 * e₀ + Cen * a ^ 2 * ℓ ^ een *
        (S.actualChargeData hm hM s.val).energyError E (a / 2) k (pre k) p + rem k := by
    rw [hbridge.1, hbridge.2] at henergy
    rw [S.actualChargeScanRound_meanEnergy]
    exact henergy
  have hg : 0 < g := div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  refine ⟨s, p, hp, hQ, ?_⟩
  apply div_le_div_of_nonneg_right _ (half_pos hg).le
  linarith

end TNLean.PEPS.AreaLaw.Scan.CollarScan
