/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualTransportEstimates
import TNLean.PEPS.AreaLaw.Scan.Defs
import QICLean.Representation.ReplicaTransport.FiniteFamily

/-!
# Common transport errors for the actual finite sequence of rounds

The round index is `Fin (2 * S.n * S.m)`. Round `j` has the actual recursive history
of length `j.val / 2`, with a deterministic fill at even indices and the actual
padded charge choices at odd indices. Blank slots are retained.

One application of finite-family transport chooses nonnegative common errors before
all round indices, replica counts, supplied vectors, interpolation points and energy
eigenvalues. The same actual band count and labelled augmented truncated Hamiltonian
are used throughout. All geometric and analytic premises are derived from their
existing producers. Physical and auxiliary dimensions are fixed before the errors;
this is not a limit over systems whose dimensions grow with the replica count.

Only the energy conclusion assumes a replica-energy eigenvector equation. At zero
replicas the copy mean is zero, so a nonzero supplied eigenvector has eigenvalue zero.
No physical prevector, ground energy identification, comparator, literal sphere measure,
normalized scanner coefficient or complete scanner is constructed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
Proposition 7.4, `06-transport.tex`, lines 377–434, and the interleaved actual
scanner in `08-scanner.tex`, lines 83–154, at `openai/math@adc7f124`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open TensorPower TensorPower.ReplicaTransport

section Family

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable (S : CollarScan V I)

/-- Histories count completed fill/charge pairs, as in `08-scanner.tex`, lines 145–154. -/
abbrev actualRoundHistory (j : Fin (2 * S.n * S.m)) : Type :=
  History S.K S.m S.M (j.val / 2)

/-- Even rounds fill deterministically; odd rounds keep every padded charge choice.
The distinction is round parity, independently of the physical side scheduled by a fill. -/
def actualRoundChoice (j : Fin (2 * S.n * S.m)) : S.actualRoundHistory j → Type :=
  if IsChargeRound j.val then fun _ => ChargeChoices S.K S.M else fun _ => Unit

instance (j : Fin (2 * S.n * S.m)) (h : S.actualRoundHistory j) :
    Fintype (S.actualRoundChoice j h) := by
  unfold actualRoundChoice
  split <;> infer_instance

instance (j : Fin (2 * S.n * S.m)) (h : S.actualRoundHistory j) :
    DecidableEq (S.actualRoundChoice j h) := by
  unfold actualRoundChoice
  split <;> infer_instance

/-- The actual finite family, without relabelling or reassociating its history trees. -/
def actualRoundData (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m)) :
    TransportData (V ⊕ Bool) S.K (S.actualRoundHistory j) (S.actualRoundChoice j) :=
  if hj : IsChargeRound j.val then
    by simpa only [actualRoundChoice, ite_eq_left hj] using S.actualChargeData hm hM (j.val / 2)
  else
    by simpa only [actualRoundChoice, ite_eq_right hj] using S.actualFillData hm hM (j.val / 2)

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I] in
/-- Every indexed round is within the physical horizon, including the final charge. -/
theorem actualRoundHistory_length_add_one_le (j : Fin (2 * S.n * S.m)) :
    j.val / 2 + 1 ≤ S.n * S.m := by
  have hj : j.val < 2 * (S.n * S.m) := calc
    j.val < 2 * S.n * S.m := j.isLt
    _ = 2 * (S.n * S.m) := Nat.mul_assoc 2 S.n S.m
  omega

/-- Actual positive history weights, partitions and moves establish admissibility
for both kinds of round. No transport certificate is supplied. -/
theorem actualRoundData_isAdmissible (hm : 0 < S.m) (hM : 0 < S.M)
    (j : Fin (2 * S.n * S.m)) : (S.actualRoundData hm hM j).IsAdmissible := by
  by_cases hj : IsChargeRound j.val
  · simpa only [actualRoundData, actualRoundChoice, ite_eq_left hj, dite_eq_left hj] using
      S.actualChargeData_isAdmissible hm hM (j.val / 2)
  · simpa only [actualRoundData, actualRoundChoice, ite_eq_right hj, dite_eq_right hj] using
      S.actualFillData_isAdmissible hm hM (j.val / 2)

end Family

/-- A single nonnegative error pair works for every actual fill and charge round.
The logarithmic bound holds at every replica count, including zero. The energy
hypothesis occurs only within its own clause; the integrated entropy estimate includes
both endpoints. All physical support, commutation and dimension premises are derived. -/
theorem actualRounds_transport_domainGraph :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {Λ T : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
        [NeZero q] [LinearOrder (AdmissibleSupport Λ R)]
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
        (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
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
        let E := S.actualEnergyTerms h Ω Δ L aux
        let ℓ := transportLogDimBound q S.r₀
        let Hbar := fun k => copyMean n k
          (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i))
        ∃ (β rem : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧
          (∀ k, 0 ≤ β k) ∧ (∀ k, 0 ≤ rem k) ∧
          (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧ Tendsto rem atTop (𝓝 0) ∧
          ∀ (j : Fin (2 * S.n * S.m)) (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
            (∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun p' => -Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k p') pre))
                ((D j).exactDerivative n (a / 2) k pre p) p ∧
              (k : ℝ) * a * (D j).entropyGain n (a / 2) k pre p -
                  Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k ≤
                (D j).exactDerivative n (a / 2) k pre p ∧
              ∀ E₀ : ℝ, Hbar k *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector ((D j).rootPath n (a / 2) k p) pre
                (star v ⬝ᵥ (Hbar k *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een *
                    (D j).energyError E (a / 2) k pre p + rem k) ∧
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              ∫ p in p₀..p₁, ((k : ℝ) * a * (D j).entropyGain n (a / 2) k pre p -
                  Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k) ≤
                Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k p₀) pre) -
                  Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k p₁) pre) := by
  classical
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, htransport⟩ := transport_finite_family
  refine ⟨c₀, Cent, eent, Cen, een, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    L hn hr hDpos hD hL hC hrows hclear a ha haℓ
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
  let n := augmentedDimensions (V := Site Λ) q aux
  let D := S.actualRoundData hm hM
  let E := S.actualEnergyTerms h Ω Δ L aux
  let Hbar := fun k => copyMean n k
    (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i))
  have hq : 1 ≤ q := NeZero.pos q
  have hE := S.actualEnergyTerms_spec h Ω hgraph hanchor hΔ hΩ L aux
  have hcompat : ∀ j, (D j).SupportCompatible E := by
    intro j
    have hs := S.actualRoundHistory_length_add_one_le j
    by_cases hj : IsChargeRound j.val
    · simpa only [D, actualRoundData, actualRoundChoice, ite_eq_left hj, dite_eq_left hj] using
        S.chargeTransportData_supportCompatible_domainGraph hT hgraph hdepth
          (historyMeanTree S.K S.m S.M hm hM (j.val / 2))
          (fun _ => chargeChoiceTree S.K S.M hM)
          hn hs hr hDpos hD hL hrows hclear n E (fun _ => rfl)
    · simpa only [D, actualRoundData, actualRoundChoice, ite_eq_right hj, dite_eq_right hj] using
        S.fillTransportData_supportCompatible_domainGraph hT hgraph hdepth
          (historyMeanTree S.K S.m S.M hm hM (j.val / 2))
          hn hs hr hDpos hD hL hrows hclear n E (fun _ => rfl)
  have ht : 0 ≤ a / 2 := (half_pos ha).le
  have hcomm : ∀ j k, (D j).CrossBandCommute n (a / 2) k := by
    intro j k
    by_cases hj : IsChargeRound j.val
    · simpa only [D, actualRoundData, actualRoundChoice, ite_eq_left hj, dite_eq_left hj] using
        S.chargeTransportData_crossBandCommute
          (historyMeanTree S.K S.m S.M hm hM (j.val / 2))
          (fun _ => chargeChoiceTree S.K S.M hM) n ht k
    · simpa only [D, actualRoundData, actualRoundChoice, ite_eq_right hj, dite_eq_right hj] using
        S.fillTransportData_crossBandCommute
          (historyMeanTree S.K S.m S.M hm hM (j.val / 2)) n ht k
  have hmove : ∀ j hist c g, logDim n ((D j).move hist c g).subsystem ≤
      transportLogDimBound q S.r₀ := by
    intro j
    by_cases hj : IsChargeRound j.val
    · simpa only [D, actualRoundData, actualRoundChoice, ite_eq_left hj, dite_eq_left hj] using
        S.chargeTransportData_logDim_move_le_domainGraph hgraph
          (historyMeanTree S.K S.m S.M hm hM (j.val / 2))
          (fun _ => chargeChoiceTree S.K S.M hM) n hq (fun _ => rfl)
    · simpa only [D, actualRoundData, actualRoundChoice, ite_eq_right hj, dite_eq_right hj] using
        S.fillTransportData_logDim_move_le
          (historyMeanTree S.K S.m S.M hm hM (j.val / 2)) n hq (fun _ => rfl)
  have hsplit : ∀ j i, ((D j).splitLeaves E i).Nonempty →
      logDim n (E.support i) ≤ transportLogDimBound q S.r₀ := by
    intro j
    by_cases hj : IsChargeRound j.val
    · simpa only [D, actualRoundData, actualRoundChoice, ite_eq_left hj, dite_eq_left hj] using
        S.chargeTransportData_logDim_support_le_domainGraph hgraph
          (historyMeanTree S.K S.m S.M hm hM (j.val / 2))
          (fun _ => chargeChoiceTree S.K S.M hM)
          n hq (fun _ => rfl) hL E (fun _ => rfl)
    · simpa only [D, actualRoundData, actualRoundChoice, ite_eq_right hj, dite_eq_right hj] using
        S.fillTransportData_logDim_support_le_domainGraph hgraph
          (historyMeanTree S.K S.m S.M hm hM (j.val / 2))
          n hq (fun _ => rfl) hL E (fun _ => rfl)
  obtain ⟨β, rem, Cβ, hCβ, hβ0, hrem0, hβ, hrem, hresult⟩ := htransport n D E
    (S.actualRoundData_isAdmissible hm hM) hE.1 hE.2.1 hE.2.2 hcompat
    ha (one_le_transportLogDimBound hq S.r₀) haℓ hcomm hmove hsplit
  have henergy (k : ℕ) : E.replicaEnergy k = Hbar k :=
    S.replicaEnergy_actualEnergyTerms h Ω Δ L aux k
  refine ⟨β, rem, Cβ, hCβ, hβ0, hrem0, hβ, hrem, ?_⟩
  simpa only [henergy] using hresult

end TNLean.PEPS.AreaLaw.Scan.CollarScan
