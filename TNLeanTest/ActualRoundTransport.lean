/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport
import TNLean.PEPS.AreaLaw.Scan.FillTransportEndpoints

/-!
# Dependent actual-round family regressions

The exact transport signature fixes one error pair before every round, count,
vector, interpolation parameter and conditional eigenvalue. Concrete round indices
check the fill/charge convention, dependent history lengths, real choice types,
empty families, final-round horizon, adjacent roots and zero-copy energy boundary.
The endpoint specialization uses the same errors for the entire finite family.
-/

set_option autoImplicit false

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy
open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Scan
open TensorPower TensorPower.ReplicaTransport

noncomputable section
namespace TNLeanTest.ActualRoundTransport

-- Exact all-round signature; no physical input or geometric premise is replaced by a certificate.
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
                  Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k p₁) pre) :=
  CollarScan.actualRounds_transport_domainGraph

section DependentFamily

variable {V I : Type*}
variable (S : CollarScan V I)

-- The first pair has no completed charges, and the next pair has exactly one.
example (h0 : 0 < 2 * S.n * S.m) :
    S.actualRoundHistory ⟨0, h0⟩ = History S.K S.m S.M 0 := rfl

example (h1 : 1 < 2 * S.n * S.m) :
    S.actualRoundHistory ⟨1, h1⟩ = History S.K S.m S.M 0 := rfl

example (h2 : 2 < 2 * S.n * S.m) :
    S.actualRoundHistory ⟨2, h2⟩ = History S.K S.m S.M 1 := rfl

example (h3 : 3 < 2 * S.n * S.m) :
    S.actualRoundHistory ⟨3, h3⟩ = History S.K S.m S.M 1 := rfl

example (h0 : 0 < 2 * S.n * S.m) (hist : S.actualRoundHistory ⟨0, h0⟩) :
    S.actualRoundChoice ⟨0, h0⟩ hist = Unit := rfl

example (h1 : 1 < 2 * S.n * S.m) (hist : S.actualRoundHistory ⟨1, h1⟩) :
    S.actualRoundChoice ⟨1, h1⟩ hist = ChargeChoices S.K S.M := rfl

example (h2 : 2 < 2 * S.n * S.m) (hist : S.actualRoundHistory ⟨2, h2⟩) :
    S.actualRoundChoice ⟨2, h2⟩ hist = Unit := rfl

example (h3 : 3 < 2 * S.n * S.m) (hist : S.actualRoundHistory ⟨3, h3⟩) :
    S.actualRoundChoice ⟨3, h3⟩ hist = ChargeChoices S.K S.M := rfl

-- Instance synthesis works before round parity or history is chosen.
example (j : Fin (2 * S.n * S.m)) (hist : S.actualRoundHistory j) :
    Fintype (S.actualRoundChoice j hist) := inferInstance

example (j : Fin (2 * S.n * S.m)) (hist : S.actualRoundHistory j) :
    DecidableEq (S.actualRoundChoice j hist) := inferInstance

example (j : Fin (2 * S.n * S.m)) :
    Fintype.card (S.actualRoundHistory j) =
      S.m ^ S.K * ((2 * S.M) ^ S.K) ^ (j.val / 2) :=
  card_history S.K S.m S.M (j.val / 2)

variable [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

-- Both actual trees, including blank choices, survive the dependent interleaving.
example (hm : 0 < S.m) (hM : 0 < S.M) (h0 : 0 < 2 * S.n * S.m) :
    S.actualRoundData hm hM ⟨0, h0⟩ = S.actualFillData hm hM 0 := by
  simp [CollarScan.actualRoundData, CollarScan.actualRoundChoice, IsChargeRound]

example (hm : 0 < S.m) (hM : 0 < S.M) (h1 : 1 < 2 * S.n * S.m) :
    S.actualRoundData hm hM ⟨1, h1⟩ = S.actualChargeData hm hM 0 := by
  simp [CollarScan.actualRoundData, CollarScan.actualRoundChoice, IsChargeRound]

example (hm : 0 < S.m) (hM : 0 < S.M) (h2 : 2 < 2 * S.n * S.m) :
    S.actualRoundData hm hM ⟨2, h2⟩ = S.actualFillData hm hM 1 := by
  simp [CollarScan.actualRoundData, CollarScan.actualRoundChoice, IsChargeRound]

example (hm : 0 < S.m) (hM : 0 < S.M) (h3 : 3 < 2 * S.n * S.m) :
    S.actualRoundData hm hM ⟨3, h3⟩ = S.actualChargeData hm hM 1 := by
  simp [CollarScan.actualRoundData, CollarScan.actualRoundChoice, IsChargeRound]

-- The generic parity branches do not rely on evaluating a small concrete round.
example (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (hj : IsChargeRound j.val) :
    HEq (S.actualRoundData hm hM j) (S.actualChargeData hm hM (j.val / 2)) := by
  simp only [CollarScan.actualRoundData, CollarScan.actualRoundChoice,
    ite_eq_left hj, dite_eq_left hj, heq_eq_eq]

example (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (hj : ¬IsChargeRound j.val) :
    HEq (S.actualRoundData hm hM j) (S.actualFillData hm hM (j.val / 2)) := by
  simp only [CollarScan.actualRoundData, CollarScan.actualRoundChoice,
    ite_eq_right hj, dite_eq_right hj, heq_eq_eq]

-- The split-leaf operation also survives the abstract dependent casts.
example (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (n : V ⊕ Bool → ℕ) {ι : Type*} (E : EnergyTerms (V ⊕ Bool) n ι)
    (i : ι) (hj : IsChargeRound j.val) :
    ((S.actualRoundData hm hM j).splitLeaves E i).card =
      ((S.actualChargeData hm hM (j.val / 2)).splitLeaves E i).card := by
  simp only [CollarScan.actualRoundData, CollarScan.actualRoundChoice,
    ite_eq_left hj, dite_eq_left hj]

example (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m))
    (n : V ⊕ Bool → ℕ) {ι : Type*} (E : EnergyTerms (V ⊕ Bool) n ι)
    (i : ι) (hj : ¬IsChargeRound j.val) :
    ((S.actualRoundData hm hM j).splitLeaves E i).card =
      ((S.actualFillData hm hM (j.val / 2)).splitLeaves E i).card := by
  simp only [CollarScan.actualRoundData, CollarScan.actualRoundChoice,
    ite_eq_right hj, dite_eq_right hj]

section RoundIndices

omit [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

-- Charge choices keep both sides and every padded slot; no positive-band premise is added.
example (h1 : 1 < 2 * S.n * S.m) (hist : S.actualRoundHistory ⟨1, h1⟩) :
    Fintype.card (S.actualRoundChoice ⟨1, h1⟩ hist) = (2 * S.M) ^ S.K := by
  change Fintype.card (Fin S.K → Bool × Fin S.M) = (2 * S.M) ^ S.K
  simp

-- Empty round domains require no artificial nonempty-family assumption.
example (hn : S.n = 0) : IsEmpty (Fin (2 * S.n * S.m)) := by
  simp only [hn, Nat.mul_zero, Nat.zero_mul]
  infer_instance

example (hm : S.m = 0) : IsEmpty (Fin (2 * S.n * S.m)) := by
  simp only [hm, Nat.mul_zero]
  infer_instance

-- The final charge uses the preceding completed pair, and is inside the horizon.
example (hnm : 0 < S.n * S.m) :
    (2 * S.n * S.m - 1) / 2 + 1 = S.n * S.m := by
  rw [Nat.mul_assoc]
  omega

example (hnm : 0 < S.n * S.m) : IsChargeRound (2 * S.n * S.m - 1) := by
  unfold IsChargeRound
  rw [Nat.mul_assoc]
  omega

example (j : Fin (2 * S.n * S.m)) : j.val / 2 + 1 ≤ S.n * S.m :=
  S.actualRoundHistory_length_add_one_le j

end RoundIndices

example (hm : 0 < S.m) (hM : 0 < S.M) (j : Fin (2 * S.n * S.m)) :
    (S.actualRoundData hm hM j).IsAdmissible :=
  S.actualRoundData_isAdmissible hm hM j

-- Matrix adjacency uses the original recursive trees, not just matching scalar weights.
example (hm : 0 < S.m) (hM : 0 < S.M)
    (h0 : 0 < 2 * S.n * S.m) (h1 : 1 < 2 * S.n * S.m)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (S.actualRoundData hm hM ⟨0, h0⟩).rootPath n t k 1 =
      (S.actualRoundData hm hM ⟨1, h1⟩).rootPath n t k 0 := by
  simpa [CollarScan.actualRoundData, CollarScan.actualRoundChoice, IsChargeRound,
    CollarScan.actualChargeData] using
      S.actualFillData_rootPath_one_eq_charge_zero hm hM 0 n ht k

example (hm : 0 < S.m) (hM : 0 < S.M)
    (h1 : 1 < 2 * S.n * S.m) (h2 : 2 < 2 * S.n * S.m)
    (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (S.actualRoundData hm hM ⟨1, h1⟩).rootPath n t k 1 =
      (S.actualRoundData hm hM ⟨2, h2⟩).rootPath n t k 0 := by
  simpa [CollarScan.actualRoundData, CollarScan.actualRoundChoice, IsChargeRound,
    CollarScan.actualChargeData] using
      S.charge_rootPath_one_eq_actualFillData_zero hm hM 0 n ht k

end DependentFamily

section ZeroCopies

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J Δ : ℝ}
variable (aux : Bool → ℕ)
variable (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
variable (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (L : ℕ)

-- The actual term family retains the copy-mean convention at zero copies.
example : (S.actualEnergyTerms h Ω Δ L aux).replicaEnergy 0 = 0 := by
  rw [CollarScan.replicaEnergy_actualEnergyTerms]
  simp [copyMean]

-- A nonzero physical energy cannot be silently substituted at zero copies.
example (pre : Config 0 (fun v => Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ)
    (hne : pre ≠ 0) (E₀ : ℝ)
    (heig : copyMean (augmentedDimensions (V := Site Λ) q aux) 0
        (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ L i)) *ᵥ pre =
      (E₀ : ℂ) • pre) : E₀ = 0 := by
  have hz : (E₀ : ℂ) • pre = 0 := by simpa [copyMean] using heig.symm
  have hE : (E₀ : ℂ) = 0 := (smul_eq_zero.mp hz).resolve_right hne
  exact_mod_cast hE

end ZeroCopies

-- One common error also works on the full interval and all degenerate intervals.
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
        ∃ (β : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧ (∀ k, 0 ≤ β k) ∧
          (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧
          ∀ (j : Fin (2 * S.n * S.m)) (r : ℕ) (pre : Config r (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace r (fun v => Fin (n v)) → pre ≠ 0 →
            (∫ p in (0 : ℝ)..1, ((r : ℝ) * a * (D j).entropyGain n (a / 2) r pre p -
                Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r) ≤
              Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) r 0) pre) -
                Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) r 1) pre)) ∧
            ∀ p₀ ∈ Icc (0 : ℝ) 1,
              (∫ p in p₀..p₀, ((r : ℝ) * a * (D j).entropyGain n (a / 2) r pre p -
                Cent * r * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β r)) ≤ 0 := by
  obtain ⟨c₀, Cent, eent, _, _, hc₀, htransport⟩ :=
    CollarScan.actualRounds_transport_domainGraph
  refine ⟨c₀, Cent, eent, hc₀, ?_⟩
  intro Λ T q R J Δ _ _ aux _ h Ω S hT hgraph hdepth hanchor hΔ hΩ
    L hn hr hDpos hD hL hC hrows hclear a ha haℓ
  obtain ⟨β, _, Cβ, hCβ, hβ0, _, hβ, _, hresult⟩ :=
    htransport aux h Ω S hT hgraph hdepth hanchor
      hΔ hΩ hn hr hDpos hD hL hC hrows hclear ha haℓ
  refine ⟨β, Cβ, hCβ, hβ0, hβ, ?_⟩
  intro j r pre hpre hne
  have hint := (hresult j r pre hpre hne).2
  refine ⟨hint 0 1 (le_refl 0) zero_le_one (le_refl 1), ?_⟩
  intro p₀ hp₀
  simpa only [sub_self] using hint p₀ p₀ hp₀.1 (le_refl p₀) hp₀.2

end TNLeanTest.ActualRoundTransport
