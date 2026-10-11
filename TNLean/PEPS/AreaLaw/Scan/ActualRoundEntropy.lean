/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport
import TNLean.PEPS.AreaLaw.Scan.FillTransportEndpoints

/-!
# Entropy summed over the actual fill and charge rounds

Successive roots agree by the actual history-tree substitution identities. Summing
the logarithmic norm differences therefore leaves the initial completed-history root
and the root after `S.n * S.m` charges. The identity allows an empty round family,
zero replicas and a zero supplied vector.

For a nonzero symmetric supplied vector, the common transport error is paid exactly
`2 * S.n * S.m` times. The constants are chosen before the scan and the logarithmic
error before all replica counts and vectors. No initial or final norm comparison,
physical prevector, energy equation or defect-selection conclusion is assumed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 442–457, at `openai/math@adc7f124`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open TensorPower TensorPower.ReplicaTransport

section Roots

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable (S : CollarScan V I)

private def actualBoundaryRoot (hm : 0 < S.m) (hM : 0 < S.M)
    (n : V ⊕ Bool → ℕ) (t : ℝ) (k r : ℕ) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  if IsChargeRound r then (S.actualChargeData hm hM (r / 2)).rootPath n t k 0
  else (S.actualFillData hm hM (r / 2)).rootPath n t k 0

private theorem actualBoundaryRoot_even (hm : 0 < S.m) (hM : 0 < S.M)
    (n : V ⊕ Bool → ℕ) (t : ℝ) (k r : ℕ) :
    S.actualBoundaryRoot hm hM n t k (2 * r) =
      (S.actualFillData hm hM r).rootPath n t k 0 := by
  have hcharge : ¬IsChargeRound (2 * r) := by
    simp [IsChargeRound, Nat.mul_mod]
  have hstage : 2 * r / 2 = r := by omega
  simp only [actualBoundaryRoot, if_neg hcharge, hstage]

private theorem actualRoundData_rootPath_zero_eq_boundary
    (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (n : V ⊕ Bool → ℕ) (t : ℝ) (k : ℕ) :
    (S.actualRoundData hm hM j).rootPath n t k 0 =
      S.actualBoundaryRoot hm hM n t k j.val := by
  refine S.actualRoundData_induction hm hM j
    (fun _ _ _ D => D.rootPath n t k 0 = S.actualBoundaryRoot hm hM n t k j.val) ?_ ?_
  · intro hj
    simp only [actualBoundaryRoot, if_pos hj]
  · intro hj
    simp only [actualBoundaryRoot, if_neg hj]

private theorem actualRoundData_rootPath_one_eq_boundary
    (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (S.actualRoundData hm hM j).rootPath n t k 1 =
      S.actualBoundaryRoot hm hM n t k (j.val + 1) := by
  refine S.actualRoundData_induction hm hM j
    (fun _ _ _ D => D.rootPath n t k 1 =
      S.actualBoundaryRoot hm hM n t k (j.val + 1)) ?_ ?_
  · intro hj
    have hj' : ¬IsChargeRound (j.val + 1) := by
      unfold IsChargeRound at *
      omega
    have hs : (j.val + 1) / 2 = j.val / 2 + 1 := by
      unfold IsChargeRound at hj
      omega
    simp only [actualBoundaryRoot, if_neg hj', hs]
    exact S.charge_rootPath_one_eq_actualFillData_zero hm hM (j.val / 2) n ht k
  · intro hj
    have hj' : IsChargeRound (j.val + 1) := by
      unfold IsChargeRound at *
      omega
    have hs : (j.val + 1) / 2 = j.val / 2 := by
      unfold IsChargeRound at hj
      omega
    simp only [actualBoundaryRoot, if_pos hj', hs]
    exact S.actualFillData_rootPath_one_eq_charge_zero hm hM (j.val / 2) n ht k

/-- Every actual round ends at the root starting the next round. This follows
from the fill and charge identities, with no supplied adjacency hypothesis. -/
theorem actualRoundData_rootPath_one_eq_succ_zero
    (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (hj : j.val + 1 < 2 * S.n * S.m)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (S.actualRoundData hm hM j).rootPath n t k 1 =
      (S.actualRoundData hm hM ⟨j.val + 1, hj⟩).rootPath n t k 0 := by
  rw [S.actualRoundData_rootPath_one_eq_boundary hm hM j n ht k,
    S.actualRoundData_rootPath_zero_eq_boundary hm hM ⟨j.val + 1, hj⟩ n t k]

/-- The last actual charge ends at the completed-history root after exactly
`S.n * S.m` charges. -/
theorem actualRoundData_rootPath_one_of_last
    (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (hj : j.val + 1 = 2 * S.n * S.m)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (S.actualRoundData hm hM j).rootPath n t k 1 =
      (S.actualFillData hm hM (S.n * S.m)).rootPath n t k 0 := by
  rw [S.actualRoundData_rootPath_one_eq_boundary hm hM j n ht k, hj, Nat.mul_assoc]
  exact S.actualBoundaryRoot_even hm hM n t k (S.n * S.m)

/-- The logarithmic norm differences of all `2 * S.n * S.m` actual rounds
telescope to the roots before the first fill and after the last charge
(`08-scanner.tex`, line 457). Empty families and zero replicas are included;
neither nonvanishing nor symmetry of the supplied vector is needed. -/
theorem sum_actualRoundData_logNormSq_sub
    (hm : 0 < S.m) (hM : 0 < S.M)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) :
    ∑ j : Fin (2 * S.n * S.m),
        (Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t k 0) pre) -
          Real.log (Transport.filteredNormSq ((S.actualRoundData hm hM j).rootPath n t k 1) pre)) =
      Real.log (Transport.filteredNormSq ((S.actualFillData hm hM 0).rootPath n t k 0) pre) -
        Real.log (Transport.filteredNormSq
          ((S.actualFillData hm hM (S.n * S.m)).rootPath n t k 0) pre) := by
  let F : ℕ → ℝ := fun r =>
    Real.log (Transport.filteredNormSq (S.actualBoundaryRoot hm hM n t k r) pre)
  have hsum : (∑ j : Fin (2 * S.n * S.m), (F j.val - F (j.val + 1))) =
      F 0 - F (2 * S.n * S.m) := by
    rw [Fin.sum_univ_eq_sum_range (fun r => F r - F (r + 1)), Finset.sum_range_sub']
  have hzero (j : Fin (2 * S.n * S.m)) :=
    S.actualRoundData_rootPath_zero_eq_boundary hm hM j n t k
  have hone (j : Fin (2 * S.n * S.m)) :=
    S.actualRoundData_rootPath_one_eq_boundary hm hM j n ht k
  simp only [hzero, hone]
  change (∑ j : Fin (2 * S.n * S.m), (F j.val - F (j.val + 1))) = _
  rw [hsum]
  change Real.log (Transport.filteredNormSq (S.actualBoundaryRoot hm hM n t k (2 * 0)) pre) -
      Real.log (Transport.filteredNormSq (S.actualBoundaryRoot hm hM n t k (2 * S.n * S.m)) pre) = _
  rw [Nat.mul_assoc, S.actualBoundaryRoot_even, S.actualBoundaryRoot_even]

/-- The actual history geometry gives the cross-band commutation required
for integrability of each round's entropy gain. -/
theorem actualRoundData_crossBandCommute
    (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (S.actualRoundData hm hM j).CrossBandCommute n t k := by
  refine S.actualRoundData_induction hm hM j
    (fun _ _ _ D => D.CrossBandCommute n t k) ?_ ?_
  · intro _
    exact S.chargeTransportData_crossBandCommute
      (historyMeanTree S.K S.m S.M hm hM (j.val / 2))
      (fun _ => chargeChoiceTree S.K S.M hM) n ht k
  · intro _
    exact S.fillTransportData_crossBandCommute
      (historyMeanTree S.K S.m S.M hm hM (j.val / 2)) n ht k

end Roots

/-- Integrating every actual fill and charge gives the initial-to-final logarithmic
norm difference plus exactly `2 * S.n * S.m` copies of the common error
(`08-scanner.tex`, lines 442–457). The supplied vector is nonzero and symmetric;
no physical prevector, energy identification or norm comparison is required. -/
theorem actualRounds_entropy_integral_le_domainGraph :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
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
                  (Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β k) := by
  classical
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, htransport⟩ := actualRounds_transport_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    L hn hr hDpos hD hL hC hrows hclear a ha haℓ
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hC (Nat.succ_le_iff.mpr hn) hDpos
  let n := augmentedDimensions (V := Site Λ) q aux
  let D := S.actualRoundData hm hM
  let ℓ := transportLogDimBound q S.r₀
  obtain ⟨β, rem, Cβ, hCβ, hβ0, hrem0, hβ, hrem, hround⟩ :=
    htransport aux h Ω S hT hgraph hdepth hanchor hΔ hΩ hn hr hDpos hD hL hC
      hrows hclear ha haℓ
  refine ⟨β, Cβ, hCβ, hβ0, hβ, ?_⟩
  intro k pre hpre hne
  let err := Cent * k * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent + β k
  have ht : 0 ≤ a / 2 := (half_pos ha).le
  have hstep (j : Fin (2 * S.n * S.m)) :
      (k : ℝ) * a * (∫ p in (0 : ℝ)..1, (D j).entropyGain n (a / 2) k pre p) ≤
        Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k 0) pre) -
          Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k 1) pre) + err := by
    have hint := (D j).intervalIntegrable_entropyGain
      (S.actualRoundData_isAdmissible hm hM j) ht
      (S.actualRoundData_crossBandCommute hm hM j n ht k) hne
    have hbound := (hround j k pre hpre hne).2 0 1 le_rfl zero_le_one le_rfl
    rw [intervalIntegral.integral_sub ((hint.const_mul _).sub intervalIntegrable_const)
        intervalIntegrable_const,
      intervalIntegral.integral_sub (hint.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul] at hbound
    simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hbound
    dsimp only [err]
    linarith
  calc
    (k : ℝ) * a * ∑ j : Fin (2 * S.n * S.m),
        ∫ p in (0 : ℝ)..1, (D j).entropyGain n (a / 2) k pre p =
        ∑ j : Fin (2 * S.n * S.m),
          (k : ℝ) * a * (∫ p in (0 : ℝ)..1, (D j).entropyGain n (a / 2) k pre p) :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ j : Fin (2 * S.n * S.m),
        (Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k 0) pre) -
          Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k 1) pre) + err) :=
      Finset.sum_le_sum fun j _ => hstep j
    _ = _ := by
      rw [Finset.sum_add_distrib, S.sum_actualRoundData_logNormSq_sub hm hM n ht k pre]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
