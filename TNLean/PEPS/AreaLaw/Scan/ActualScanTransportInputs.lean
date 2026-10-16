/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualHistoryFacts
import TNLean.PEPS.AreaLaw.Scan.ActualRoundEntropy
import TNLean.PEPS.AreaLaw.Scan.ActualRoundParameterIntegral
import TNLean.PEPS.AreaLaw.Scan.Budgets

/-!
# The transport inputs of the actual collar scan (Proposition 7.4)

The conclusions of Proposition 7.4 (`prop:transport`) that the scanner estimate uses are
collected in `ScanTransportInputs`: the leaf measures are finite and have mass `1/2` in the
interior, the charge defect is measurable, `log N(p)²` is continuous on `[0, 1]` and
differentiable on `(0, 1)`, the entropy-gain and energy estimates hold with the scanner's
constants `κ.C` and `κ.C_l`, and successive rounds share their endpoint norms.
`ScanTransportInputs.toScanInputs` completes them to `ScanInputs` from the conclusions of
Proposition 8.1.

For the actual rounds of one physical collar scan these fields are proved from the
transport estimates of the actual rounds. The rounds are interleaved fills and charges; each
is the literal round of the corresponding transport datum. The hypotheses are those of
Proposition 7.4: the supplied vector is a nonzero element of the symmetric subspace at every
replica count, the product `aℓ` of the per-band weight and the logarithmic support cap is
small, and for the energy estimate the supplied vector is an eigenvector of the replica mean
of the truncated Hamiltonian with the truncated ground energy. At zero replicas that mean is
zero, so the eigenvector equation is required only for positive replica counts; at zero
replicas the energy estimate uses the eigenvalue zero.

The source's transport constants are universal, and the support dimensions enter them only
through `ℓ = 1 + (2r₀ + 1)² log q`. With `r₀ = ⌈C_tr log² n⌉`, `ℓ` is at most a fixed multiple
of `(log n)⁴`, so a scanner constant `κ.C` and power `κ.C_l` above explicit thresholds absorb
the transport coefficients `C ℓ^C` into `κ.C (log n)^{κ.C_l}`.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.ScanTransportInputs`: the Proposition 7.4 fields of `ScanInputs`.
* `TNLean.PEPS.AreaLaw.Scan.ScanTransportInputs.toScanInputs`: completion by the
  Proposition 8.1 fields.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.actualScanRound_eq_transportScanRound`: each actual
  round is the literal round of the actual transport datum.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.exists_scanTransportInputs_actualScan`: the
  Proposition 7.4 fields for the actual rounds of every physical collar scan at the source
  scales.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 7.4 (`prop:transport`), `06-transport.tex`, lines 377–433, the scanner scales
  and rounds of `08-scanner.tex`, lines 32–59 and 83–154, and the use of Proposition 7.4 in
  the proof of Proposition 9.2, lines 416–461. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently formalized from the
  manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder
open Filter Topology Set MeasureTheory
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

/-- The conclusions of Proposition 7.4 (`prop:transport`, `06-transport.tex`, lines 377–433)
for a family of rounds with total metric weight `W`, measured against the truncated ground
state `T`, in the form of the corresponding fields of `ScanInputs`: the replica remainders,
the leaf measures with mass `2s = 1/2` in the interior (lines 393–400), the parameter
regularity of the charge defect and of `log N(p)²`, the entropy gain
(`transport:entropy-gain`), the energy estimate (`transport:energy`), and the agreement of
adjacent endpoint metrics (`08-scanner.tex`, lines 145–154 and 457–461). -/
structure ScanTransportInputs (X : ScannerExponents) (κ : ScanConstants) (n : ℕ)
    (T : ScanTruncation X κ n) {ι Θ : Type} [Fintype ι] [MeasurableSpace Θ]
    (round : Fin (X.rounds n) → ScanRound ι Θ) (W : ℝ) where
  /-- The `o_k(1)` remainder of `transport:energy`, uniform in rounds and parameters. -/
  rem : ℕ → ℝ
  rem_nonneg : ∀ k, 0 ≤ rem k
  tendsto_rem : Tendsto rem atTop (𝓝 0)
  /-- `β_k = O_fixed(log(k+2))` of `transport:entropy-gain`. -/
  β : ℕ → ℝ
  Cβ : ℝ
  β_nonneg : ∀ k, 0 ≤ β k
  β_le : ∀ k, β k ≤ Cβ * Real.log (k + 2)
  isFiniteMeasure_μOld : ∀ r k p h, IsFiniteMeasure ((round r).μOld k p h)
  isFiniteMeasure_μNew : ∀ r k p h c, IsFiniteMeasure ((round r).μNew k p h c)
  /-- The old-leaf measure has mass `1/2` for `0 < p < 1` (`06-transport.tex`,
  lines 393–400). -/
  μOld_real_univ : ∀ r k, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ h,
    ((round r).μOld k p h).real univ = 1 / 2
  /-- The new-leaf measure has mass `1/2` for `0 < p < 1` (`06-transport.tex`,
  lines 393–400). -/
  μNew_real_univ : ∀ r k, ∀ p ∈ Ioo (0 : ℝ) 1, ∀ h c,
    ((round r).μNew k p h c).real univ = 1 / 2
  aestronglyMeasurable_chargeDefect : ∀ r k,
    AEStronglyMeasurable ((round r).chargeDefect k) (volume.restrict (Ioo 0 1))
  continuousOn_logNormSq : ∀ r k, ContinuousOn ((round r).logNormSq k) (Icc 0 1)
  differentiableOn_logNormSq : ∀ r k, DifferentiableOn ℝ ((round r).logNormSq k) (Ioo 0 1)
  /-- `transport:entropy-gain`, with the band count `K` and `ℓ^C ≤ κ.C (log n)^{κ.C_l}`. -/
  entropy_gain : ∀ r k, ∀ p ∈ Ioo (0 : ℝ) 1,
    k * X.a W n * (round r).choiceGainSum k p
        - κ.C * k * X.a W n * X.K n * X.a W n ^ (1 / 4 : ℝ) * Real.log n ^ κ.Cl - β k ≤
      -deriv ((round r).logNormSq k) p
  /-- `transport:energy` with eigenvalue `\widetilde E_0`. -/
  energy : ∀ r k, ∀ p ∈ Ioo (0 : ℝ) 1,
    (round r).meanEnergy k p ≤
      2 * T.E0 + κ.C * X.a W n ^ 2 * Real.log n ^ κ.Cl * (round r).energySum k p + rem k
  /-- Adjacent endpoint metrics agree. -/
  logNormSq_succ : ∀ (r : Fin (X.rounds n)) (hr : r.val + 1 < X.rounds n) k,
    (round ⟨r.val + 1, hr⟩).logNormSq k 0 = (round r).logNormSq k 1

namespace ScanTransportInputs

variable {X : ScannerExponents} {κ : ScanConstants} {n : ℕ} {T : ScanTruncation X κ n}
  {ι Θ : Type} [Fintype ι] [MeasurableSpace Θ] {round : Fin (X.rounds n) → ScanRound ι Θ}
  {W : ℝ}

/-- Completing the conclusions of Proposition 7.4 by those of Proposition 8.1 gives
`ScanInputs`. The comparator budgets, the initial floor with its own `β'_k = O(log(k+2))`
and the terminal rough upper comparison with its own `o_k(1)` remainder are supplied; the
remainders and the logarithmic errors of the two propositions are added. -/
def toScanInputs (P : ScanTransportInputs X κ n T round W)
    (Bsh : ℝ) (Bsh_le : ∃ j ≤ X.L n, Bsh ≤ T.SQt j + n * Real.log κ.q)
    (Bexc : ℝ) (Bexc_le : Bexc ≤ 1 + κ.C * n * X.D n * Real.log κ.q)
    (rem' : ℕ → ℝ) (rem'_nonneg : ∀ k, 0 ≤ rem' k) (tendsto_rem' : Tendsto rem' atTop (𝓝 0))
    (β' : ℕ → ℝ) (Cβ' : ℝ) (β'_nonneg : ∀ k, 0 ≤ β' k)
    (β'_le : ∀ k, β' k ≤ Cβ' * Real.log (k + 2))
    (logNormSq_init : ∀ (r : Fin (X.rounds n)), r.val = 0 → ∀ k,
      (round r).logNormSq k 0 ≤ β' k)
    (logNormSq_final : ∀ (r : Fin (X.rounds n)), r.val + 1 = X.rounds n → ∀ k, 1 ≤ k →
      -(round r).logNormSq k 1 / k ≤
        2 * Real.log T.dstar - Real.log T.z + 2 * (1 / 4) * W * (2 * Bsh / T.z + 2 * Bexc) +
          rem' k) :
    ScanInputs X κ n T round W where
  Bsh := Bsh
  Bsh_le := Bsh_le
  Bexc := Bexc
  Bexc_le := Bexc_le
  rem := fun k ↦ P.rem k + rem' k
  rem_nonneg := fun k ↦ add_nonneg (P.rem_nonneg k) (rem'_nonneg k)
  tendsto_rem := by simpa using P.tendsto_rem.add tendsto_rem'
  β := fun k ↦ P.β k + β' k
  Cβ := P.Cβ + Cβ'
  β_nonneg := fun k ↦ add_nonneg (P.β_nonneg k) (β'_nonneg k)
  β_le := fun k ↦ by
    rw [add_mul]
    exact add_le_add (P.β_le k) (β'_le k)
  isFiniteMeasure_μOld := P.isFiniteMeasure_μOld
  isFiniteMeasure_μNew := P.isFiniteMeasure_μNew
  μOld_real_univ := P.μOld_real_univ
  μNew_real_univ := P.μNew_real_univ
  aestronglyMeasurable_chargeDefect := P.aestronglyMeasurable_chargeDefect
  continuousOn_logNormSq := P.continuousOn_logNormSq
  differentiableOn_logNormSq := P.differentiableOn_logNormSq
  entropy_gain := fun r k p hp ↦ by
    have := P.entropy_gain r k p hp
    linarith [β'_nonneg k]
  energy := fun r k p hp ↦ by
    have := P.energy r k p hp
    linarith [rem'_nonneg k]
  logNormSq_succ := P.logNormSq_succ
  logNormSq_init := fun r hr k ↦ (logNormSq_init r hr k).trans (by linarith [P.β_nonneg k])
  logNormSq_final := fun r hr k hk ↦
    (logNormSq_final r hr k hk).trans (by linarith [P.rem_nonneg k])

end ScanTransportInputs

/-- A coefficient `C' ℓ^{e'}` of a transport estimate is absorbed into `C (log n)^{C_l}` once
`1 ≤ ℓ ≤ A (log n)⁴`, `log n ≥ 1`, `|C'| A^{max e' 0} ≤ C` and `4 max e' 0 ≤ C_l`. -/
theorem mul_rpow_le_of_le_mul_rpow_four {C' e' ℓ A L C Cl : ℝ} (hℓ : 1 ≤ ℓ)
    (hℓA : ℓ ≤ A * L ^ (4 : ℝ)) (hL : 1 ≤ L) (hC : |C'| * A ^ max e' 0 ≤ C)
    (hCl : 4 * max e' 0 ≤ Cl) :
    C' * ℓ ^ e' ≤ C * L ^ Cl := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hL4 : 0 < L ^ (4 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hA : 0 < A := by
    by_contra hA
    have : A * L ^ (4 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hA) hL4.le
    linarith
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ
  have he : 0 ≤ max e' 0 := le_max_right _ _
  have hC0 : 0 ≤ C := (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hA.le _)).trans hC
  calc C' * ℓ ^ e' ≤ |C'| * ℓ ^ max e' 0 :=
        mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hℓ (le_max_left _ _))
          (Real.rpow_nonneg hℓ0.le _) (abs_nonneg _)
    _ ≤ |C'| * (A * L ^ (4 : ℝ)) ^ max e' 0 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hℓ0.le hℓA he) (abs_nonneg _)
    _ = (|C'| * A ^ max e' 0) * L ^ (4 * max e' 0) := by
        rw [Real.mul_rpow hA.le hL4.le, ← Real.rpow_mul hL0.le]
        ring
    _ ≤ C * L ^ Cl :=
        mul_le_mul hC (Real.rpow_le_rpow_of_exponent_le hL hCl)
          (Real.rpow_nonneg hL0.le _) hC0

/-- A derivative of `-g` gives the negated derivative of `g`. -/
theorem hasDerivAt_of_hasDerivAt_neg {g : ℝ → ℝ} {d p : ℝ}
    (hg : HasDerivAt (fun x ↦ -g x) d p) : HasDerivAt g (-d) p := by
  have h2 := hg.neg
  rwa [show (-fun x ↦ -g x) = g from funext fun x ↦ by simp] at h2

namespace CollarScan

section Bridge

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (S : CollarScan V I) (hm : 0 < S.m) (hM : 0 < S.M)
  (n : V ⊕ Bool → ℕ) [∀ v, NeZero (n v)] (E : EnergyTerms (V ⊕ Bool) n I)
  (a : ℝ) (pre : (k : ℕ) → Config k (fun v => Fin (n v)) → ℂ)

/-- Each actual round, a fill at even and a charge at odd positions, is the literal round of
the actual transport datum at the same position (`08-scanner.tex`, lines 106–107 and
416–451). -/
theorem actualScanRound_eq_transportScanRound (j : ℕ) (hj : j < 2 * S.n * S.m) :
    S.actualScanRound hm hM n E a pre j =
      transportScanRound (S.actualRoundData hm hM ⟨j, hj⟩) n E S.IsGoodOldHistory (a / 2)
        pre := by
  refine S.actualRoundData_induction hm hM ⟨j, hj⟩
    (fun _ _ _ D => S.actualScanRound hm hM n E a pre j =
      transportScanRound D n E S.IsGoodOldHistory (a / 2) pre) ?_ ?_
  · intro hc
    rw [S.actualScanRound_of_charge hm hM n E a pre hc]
    rfl
  · intro hf
    rw [S.actualScanRound_of_fill hm hM n E a pre hf]
    rfl

/-- The energy error of an actual round is nonnegative. -/
theorem actualRoundData_energyError_nonneg {a : ℝ} (ha : 0 ≤ a)
    (j : Fin (2 * S.n * S.m)) (k : ℕ) (v : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    0 ≤ (S.actualRoundData hm hM j).energyError E (a / 2) k v p := by
  classical
  let D := S.actualRoundData hm hM j
  let T := D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)
  have hadm : D.IsAdmissible := S.actualRoundData_isAdmissible hm hM j
  have ha2 : 0 ≤ a / 2 := div_nonneg ha (by norm_num)
  have hcomm : D.CrossBandCommute n (a / 2) k :=
    S.actualRoundData_crossBandCommute hm hM j n ha2 k
  change 0 ≤ D.energyError E (a / 2) k v p
  unfold TransportData.energyError
  refine Finset.sum_nonneg fun i _ ↦ mul_nonneg ?_ ?_
  · exact Finset.sum_nonneg fun j _ ↦ T.weight_nonneg j
  · refine Finset.sum_nonneg fun j _ ↦ mul_nonneg (T.weight_nonneg j) ?_
    refine MeasureTheory.integral_nonneg fun u ↦ mul_nonneg
      (Real.sinhRatioDensity_pos ⟨by norm_num, by norm_num⟩ u).le ?_
    exact realCoherentIntegral_nonneg _
      (D.posSemidef_state hadm ha2 hcomm v p j u)
      (fun _ ↦ rpow_one_div_eight_nonneg _)

/-- `log N(p)²` of an actual round is continuous in the interpolation parameter for every
nonzero supplied vector (`06-transport.tex`, lines 427–429). -/
theorem continuous_log_filteredNormSq_actualRoundData {a : ℝ} (ha : 0 ≤ a)
    (j : Fin (2 * S.n * S.m)) (k : ℕ) {v : Config k (fun v => Fin (n v)) → ℂ} (hv : v ≠ 0) :
    Continuous fun p => Real.log (Matrix.Transport.filteredNormSq
      ((S.actualRoundData hm hM j).rootPath n (a / 2) k p) v) := by
  let D := S.actualRoundData hm hM j
  have ha2 : 0 ≤ a / 2 := div_nonneg ha (by norm_num)
  have hIn := D.posDef_input (S.actualRoundData_isAdmissible hm hM j) ha2
    (S.actualRoundData_crossBandCommute hm hM j n ha2 k)
  have hA : ∀ h', (D.oldMetric n (a / 2) k h').PosDef := fun h' => hIn ⟨h', none⟩
  have hA' : ∀ h' c, (D.newMetric n (a / 2) k h' c).PosDef := fun h' c => hIn ⟨h', some c⟩
  exact (Matrix.Transport.continuous_filteredNormSq_interpPath hA hA' v).log fun q =>
    (Matrix.Transport.filteredNormSq_pos (Matrix.Transport.posDef_interpRoot hA hA' _)
      hv).ne'

/-- A property of the literal round of the actual transport datum holds for the actual round
at the same position. -/
theorem actualScanRound_of_transportScanRound
    (P : ScanRound I (CoherentSphere (SiteConfig n)) → Prop) (j : ℕ) (hj : j < 2 * S.n * S.m)
    (hP : P (transportScanRound (S.actualRoundData hm hM ⟨j, hj⟩) n E S.IsGoodOldHistory
      (a / 2) pre)) :
    P (S.actualScanRound hm hM n E a pre j) := by
  rw [S.actualScanRound_eq_transportScanRound hm hM n E a pre j hj]
  exact hP

end Bridge

open Matrix in
/-- **The transport inputs of the actual scan (Proposition 7.4).** Fix scanner exponents, a
local dimension `q` and a truncation-radius coefficient `C_tr ≥ 0`. There are a smallness
threshold `c₀ > 0` and thresholds `C₀`, `C_{l,0}` such that for every scanner constant `κ` with
`κ.C ≥ C₀` and `κ.C_l ≥ C_{l,0}`, for all sufficiently large `N`, the following holds. Let a
physical collar scan at the source scales (`scanner:scales`) with `r₀ = ⌈C_tr log² N⌉` satisfy
the source test geometry (`scanner:test-geometry`), let `Ω` be a unit vector, `Δ > 0`, and let
`W ≥ 1` be a total weight whose per-band weight `a = W/K` satisfies the smallness `aℓ ≤ c₀`
for the support cap `ℓ = 1 + (2r₀ + 1)² log q`. Let the supplied replica vectors be nonzero
and symmetric at every replica count, and at every positive replica count eigenvectors of the
replica mean of the augmented truncated Hamiltonian with eigenvalue `\widetilde E_0` of a
truncated ground state `T`. Then the actual rounds satisfy the conclusions of
Proposition 7.4 in the form `ScanTransportInputs` for `W` and `T`.

Source: `06-transport.tex`, Proposition 7.4, lines 377–433; `08-scanner.tex`, lines 32–59,
83–154 and 416–461. -/
theorem exists_scanTransportInputs_actualScan (X : ScannerExponents) {q : ℕ} [NeZero q]
    {Ctr : ℝ} (hCtr : 0 ≤ Ctr) :
    ∃ c₀ C₀ Cl₀ : ℝ, 0 < c₀ ∧ ∀ κ : ScanConstants, C₀ ≤ κ.C → Cl₀ ≤ κ.Cl →
      ∀ᶠ N : ℕ in atTop,
      ∀ {Λ T : Finset (ℤ × ℤ)} {R : ℕ} {J Δ : ℝ} [LinearOrder (AdmissibleSupport Λ R)]
        (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J) (Ω : StateSpace Λ q)
        (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (hm : 0 < S.m) (hM : 0 < S.M)
        (aux : Bool → ℕ) [∀ b, NeZero (aux b)],
        S.graph = domainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) → 0 < Δ → ‖Ω‖ = 1 →
        S.n = N → S.m = X.m N → S.K = X.K N → S.D = X.D N →
        S.r₀ = ⌈Ctr * Real.log N ^ 2⌉₊ → 0 < S.C₁ →
        (∀ d : ℕ, 1 ≤ d → d ≤ X.L N →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
          ((2 * X.L N + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
        ∀ (Tr : ScanTruncation X κ N) (W : ℝ), 1 ≤ W →
        X.a W N * transportLogDimBound q S.r₀ ≤ c₀ →
        ∀ pre : (k : ℕ) →
          Config k (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v)) → ℂ,
        (∀ k, pre k ∈
          symmetricSubspace k (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q aux v))) →
        (∀ k, pre k ≠ 0) →
        (∀ k, 1 ≤ k → copyMean (augmentedDimensions (V := Site Λ) q aux) k
            (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ (X.L N) i)) *ᵥ pre k =
          (Tr.E0 : ℂ) • pre k) →
        Nonempty (ScanTransportInputs X κ N Tr
          (fun r ↦ S.actualScanRound hm hM (augmentedDimensions (V := Site Λ) q aux)
            (S.actualEnergyTerms h Ω Δ (X.L N) aux) (X.a W N) pre r.val) W) := by
  classical
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, htransport⟩ := actualRounds_transport_domainGraph
  have hq : 1 ≤ q := NeZero.pos q
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 + (2 * Ctr + 3) ^ 2 * Real.log q := ⟨_, rfl⟩
  refine ⟨c₀, max (|Cent| * A ^ max eent 0) (|Cen| * A ^ max een 0),
    4 * max (max eent 0) (max een 0), hc₀, ?_⟩
  intro κ hκC hκCl
  obtain ⟨C₁, hscale⟩ := eventually_scaleFacts X
  filter_upwards [hscale, eventually_split_counting_scale_separation (ell := X.ell) hCtr
    X.kappa_pos X.kappa_lt_mu, eventually_ge_atTop 3,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with N hsf hsep hN3 hlog
  intro Λ T R J Δ _ hT h Ω S hm hM aux _ hgraph hdepth hanchor hΔ hΩ hSn hSm hSK hSD hSr hC
    hrows hclear Tr W hW haℓ pre hsym hpre heig
  dsimp only [roundedLogRadius] at hsep
  obtain ⟨-, hr, hDpos, hmargin, -⟩ := hsep
  have hn : 0 < S.n := by omega
  have hr' : S.r₀ ≤ S.D := by rw [hSr, hSD]; exact hr
  have hD1 : 1 ≤ S.D := by rw [hSD]; exact hDpos
  have hD4 : 4 * S.D ≤ S.m := by
    rw [hSD, hSm]
    unfold ScannerExponents.D ScannerExponents.m
    omega
  have hL : 8 * S.K * S.m ≤ X.L N := by
    rw [hSK, hSm]
    exact eight_mul_bandCount_mul_le (X.L N) (X.m N)
  have hK : (0 : ℝ) < X.K N := by
    exact_mod_cast (show 0 < X.K N by have := hsf.one_le_K; omega)
  have ha : 0 < X.a W N := div_pos (by linarith) hK
  have ha2 : 0 ≤ X.a W N / 2 := by positivity
  obtain ⟨βs, rems, Cβs, -, hβ0, hrem0, hβ, hrem, hround⟩ :=
    htransport aux h Ω S hT hgraph hdepth hanchor hΔ hΩ hn hr' hD1 hD4 hL hC hrows hclear
      ha haℓ
  -- the coefficients of Proposition 7.4 are absorbed into `κ.C (log N)^{κ.C_l}`
  have hℓ1 : 1 ≤ transportLogDimBound q S.r₀ := one_le_transportLogDimBound hq S.r₀
  have hℓA : transportLogDimBound q S.r₀ ≤ A * Real.log N ^ (4 : ℝ) := by
    have := two_mul_transportLogDimBound_le hq hCtr hN3
    rw [hSr, hA]
    linarith
  have hent : Cent * transportLogDimBound q S.r₀ ^ eent ≤ κ.C * Real.log N ^ κ.Cl :=
    mul_rpow_le_of_le_mul_rpow_four hℓ1 hℓA hlog ((le_max_left _ _).trans hκC)
      (le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)) hκCl)
  have hen : Cen * transportLogDimBound q S.r₀ ^ een ≤ κ.C * Real.log N ^ κ.Cl :=
    mul_rpow_le_of_le_mul_rpow_four hℓ1 hℓA hlog ((le_max_right _ _).trans hκC)
      (le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)) hκCl)
  have hj (r : Fin (X.rounds N)) : r.val < 2 * S.n * S.m := by
    have := r.isLt
    simp only [ScannerExponents.rounds] at this
    rw [hSn, hSm]
    exact this
  have hadm (j : Fin (2 * S.n * S.m)) := S.actualRoundData_isAdmissible hm hM j
  have hcomm (j : Fin (2 * S.n * S.m)) (k : ℕ) :=
    S.actualRoundData_crossBandCommute hm hM j (augmentedDimensions (V := Site Λ) q aux) ha2 k
  have key (P : ScanRound (AdmissibleSupport Λ R)
      (CoherentSphere (SiteConfig (augmentedDimensions (V := Site Λ) q aux))) → Prop)
      (r : Fin (X.rounds N))
      (hP : P (transportScanRound (S.actualRoundData hm hM ⟨r.val, hj r⟩)
        (augmentedDimensions (V := Site Λ) q aux) (S.actualEnergyTerms h Ω Δ (X.L N) aux)
        S.IsGoodOldHistory (X.a W N / 2) pre)) :
      P (S.actualScanRound hm hM (augmentedDimensions (V := Site Λ) q aux)
        (S.actualEnergyTerms h Ω Δ (X.L N) aux) (X.a W N) pre r.val) :=
    S.actualScanRound_of_transportScanRound hm hM _ _ _ pre P r.val (hj r) hP
  refine ⟨ScanTransportInputs.mk rems hrem0 hrem βs Cβs hβ0 hβ
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro r
    exact key
      (fun R ↦ ∀ k p h, IsFiniteMeasure (R.μOld k p h)) r
      (fun k p h ↦ isFiniteMeasure_transportScanRound_old
        (S.actualRoundData hm hM ⟨r.val, hj r⟩) _ _ _ _ pre k p h)
  · intro r
    exact key
      (fun R ↦ ∀ k p h c, IsFiniteMeasure (R.μNew k p h c)) r
      (fun k p h c ↦ isFiniteMeasure_transportScanRound_new
        (S.actualRoundData hm hM ⟨r.val, hj r⟩) _ _ _ _ pre k p h c)
  · intro r k p hp
    exact key
      (fun R ↦ ∀ h, (R.μOld k p h).real univ = 1 / 2) r
      (fun h ↦ (transportScanRound_mass _ _ _ _ _ pre (hadm _) ha2 k (hcomm _ k) (hsym k)
        (hpre k) hp h).1)
  · intro r k p hp
    exact key
      (fun R ↦ ∀ h c, (R.μNew k p h c).real univ = 1 / 2) r
      (fun h ↦ (transportScanRound_mass _ _ _ _ _ pre (hadm _) ha2 k (hcomm _ k) (hsym k)
        (hpre k) hp h).2)
  · intro r k
    exact key
      (fun R ↦ AEStronglyMeasurable (R.chargeDefect k) (volume.restrict (Ioo 0 1))) r
      (aestronglyMeasurable_transportScanRound_chargeDefect _ _ _ _ _ pre (hadm _) ha2 k
        (hcomm _ k))
  · intro r k
    exact key
      (fun R ↦ ContinuousOn (R.logNormSq k) (Icc 0 1)) r
      (S.continuous_log_filteredNormSq_actualRoundData hm hM _ ha.le _ k (hpre k)).continuousOn
  · intro r k
    refine key
      (fun R ↦ DifferentiableOn ℝ (R.logNormSq k) (Ioo 0 1)) r ?_
    intro p hp
    have hd := ((hround ⟨r.val, hj r⟩ k (pre k) (hsym k) (hpre k)).1 p hp).1
    exact (hasDerivAt_of_hasDerivAt_neg hd).differentiableAt.differentiableWithinAt
  · intro r k
    refine key
      (fun R ↦ ∀ p ∈ Ioo (0 : ℝ) 1,
        k * X.a W N * R.choiceGainSum k p
            - κ.C * k * X.a W N * X.K N * X.a W N ^ (1 / 4 : ℝ) * Real.log N ^ κ.Cl - βs k ≤
          -deriv (R.logNormSq k) p) r ?_
    intro p hp
    obtain ⟨hd, hgain, -⟩ := (hround ⟨r.val, hj r⟩ k (pre k) (hsym k) (hpre k)).1 p hp
    rw [transportScanRound_choiceGainSum _ _ _ _ _ pre (hadm _) ha2 k (hcomm _ k) p]
    have hderiv := (hasDerivAt_of_hasDerivAt_neg hd).deriv
    change _ ≤ -deriv (fun p' ↦ Real.log (Matrix.Transport.filteredNormSq
      ((S.actualRoundData hm hM ⟨r.val, hj r⟩).rootPath
        (augmentedDimensions (V := Site Λ) q aux) (X.a W N / 2) k p') (pre k))) p
    rw [hderiv, neg_neg]
    have hKc : ((S.K : ℕ) : ℝ) = X.K N := by rw [hSK]
    have hc : 0 ≤ (k : ℝ) * X.a W N * X.K N * X.a W N ^ (1 / 4 : ℝ) := by positivity
    have habs := mul_le_mul_of_nonneg_left hent hc
    have e1 : (k : ℝ) * X.a W N * X.K N * X.a W N ^ (1 / 4 : ℝ) *
        (Cent * transportLogDimBound q S.r₀ ^ eent) =
        Cent * k * X.a W N * X.K N * X.a W N ^ (1 / 4 : ℝ) *
          transportLogDimBound q S.r₀ ^ eent := by ring
    have e2 : (k : ℝ) * X.a W N * X.K N * X.a W N ^ (1 / 4 : ℝ) *
        (κ.C * Real.log N ^ κ.Cl) =
        κ.C * k * X.a W N * X.K N * X.a W N ^ (1 / 4 : ℝ) * Real.log N ^ κ.Cl := by ring
    rw [hKc] at hgain
    linarith
  · intro r k
    refine key
      (fun R ↦ ∀ p ∈ Ioo (0 : ℝ) 1,
        R.meanEnergy k p ≤
          2 * Tr.E0 + κ.C * X.a W N ^ 2 * Real.log N ^ κ.Cl * R.energySum k p + rems k)
      r ?_
    intro p hp
    obtain ⟨-, -, henergy⟩ := (hround ⟨r.val, hj r⟩ k (pre k) (hsym k) (hpre k)).1 p hp
    obtain ⟨E₀, hE₀, heigE₀⟩ : ∃ E₀ : ℝ, E₀ ≤ Tr.E0 ∧
        copyMean (augmentedDimensions (V := Site Λ) q aux) k
            (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ (X.L N) i)) *ᵥ pre k =
          (E₀ : ℂ) • pre k := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        exact ⟨0, Tr.E0_nonneg, by simp [copyMean]⟩
      · exact ⟨Tr.E0, le_rfl, heig k hk⟩
    have hb := henergy E₀ heigE₀
    rw [transportScanRound_energySum _ _ _ _ _ pre (hadm _) ha2 k (hcomm _ k)
      (Ioo_subset_Icc_self hp)]
    have hmean : (transportScanRound (S.actualRoundData hm hM ⟨r.val, hj r⟩)
        (augmentedDimensions (V := Site Λ) q aux) (S.actualEnergyTerms h Ω Δ (X.L N) aux)
        S.IsGoodOldHistory (X.a W N / 2) pre).meanEnergy k p =
        let v := Matrix.Transport.filteredVector
          ((S.actualRoundData hm hM ⟨r.val, hj r⟩).rootPath
            (augmentedDimensions (V := Site Λ) q aux) (X.a W N / 2) k p) (pre k)
        (star v ⬝ᵥ (copyMean (augmentedDimensions (V := Site Λ) q aux) k
          (augmentOperator q aux (∑ i, S.truncatedEnergyTerm h Ω Δ (X.L N) i)) *ᵥ v)).re := by
      dsimp only [transportScanRound]
      rw [S.replicaEnergy_actualEnergyTerms h Ω Δ (X.L N) aux k]
    rw [hmean]
    have herr := S.actualRoundData_energyError_nonneg hm hM
      (augmentedDimensions (V := Site Λ) q aux) (S.actualEnergyTerms h Ω Δ (X.L N) aux) ha.le
      ⟨r.val, hj r⟩ k (pre k) p
    have hc := mul_nonneg (sq_nonneg (X.a W N)) herr
    have habs := mul_le_mul_of_nonneg_left hen hc
    refine hb.trans ?_
    nlinarith
  · intro r hr k
    have hj' : r.val + 1 < 2 * S.n * S.m := by
      have := hr
      simp only [ScannerExponents.rounds] at this
      rw [hSn, hSm]
      exact this
    change (S.actualScanRound hm hM (augmentedDimensions (V := Site Λ) q aux)
        (S.actualEnergyTerms h Ω Δ (X.L N) aux) (X.a W N) pre (r.val + 1)).logNormSq k 0 =
      (S.actualScanRound hm hM (augmentedDimensions (V := Site Λ) q aux)
        (S.actualEnergyTerms h Ω Δ (X.L N) aux) (X.a W N) pre r.val).logNormSq k 1
    rw [S.actualScanRound_eq_transportScanRound hm hM _ _ _ pre (r.val + 1) hj',
      S.actualScanRound_eq_transportScanRound hm hM _ _ _ pre r.val (hj r)]
    exact congrArg (fun M ↦ Real.log (Matrix.Transport.filteredNormSq M (pre k)))
      (S.actualRoundData_rootPath_one_eq_succ_zero hm hM ⟨r.val, hj r⟩ hj' _ ha2 k).symm

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
