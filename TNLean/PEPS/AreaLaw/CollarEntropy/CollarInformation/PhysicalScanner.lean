/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.CollarEntropy.ChargePoints.Scanner
import TNLean.PEPS.AreaLaw.Scanner.Rounds.ActualHistoryFacts
import TNLean.PEPS.AreaLaw.Scanner.Statuses.ScanTruncationInputs
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# The scanner estimate for one physical system

For one gapped physical system with a collar scan at the source scales, under the source test
geometry and entropy inputs, the conclusions of Lemma 9.1 hold for the actual rounds of the scan
and those of Proposition 4.5 and Lemmas 2.1 and 3.1 hold for one truncated ground vector `Ωt`.
Hence Proposition 9.2 holds for the actual scan as soon as the conclusions of Propositions 7.4
and 8.1 (`ScanInputs`) hold for its rounds, its total weight `W` and the same `Ωt`.

`scanner_estimate_actualScan` takes the conclusions of Proposition 7.4 (`prop:transport`) and
Proposition 8.1 (`prop:comparators`) for the actual rounds as the hypothesis `ScanInputs`; the
other inputs of the proof of Proposition 9.2 are derived. This conditional route is auxiliary
and is not the source statement.
The source statement of Proposition 9.2 is proved for the original physical system as
`TNLean.PEPS.AreaLaw.Scan.CollarScan.scannerStatement`, without these fields as hypotheses
(`docs/paper-gaps/arealaw2d_scanner_inputs.tex`, which records its output-coefficient convention).

## Main results

* `TNLean.PEPS.AreaLaw.Scan.HistoryFacts.mono`: the history conclusions survive larger
  constants and a smaller sampling constant.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.scanner_estimate_actualScan`: Proposition 9.2 for the
  actual scan of one physical system, from the conclusions of Propositions 7.4 and 8.1.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 9.2 (`prop:scanner`), `08-scanner.tex`, lines 349–533, with the scales and test
  geometry of lines 21–59. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently formalized from the
  manuscript; no upstream Lean proof text is reused.
-/

open ManyBody (designatedSupport)

open scoped Matrix.Norms.L2Operator

open Filter Topology Set

open ManyBody (IsGapped groundSpace PlaneInteraction ambientDepth supDist)
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

open ManyBody (AdmissibleSupport ambientDilation planeDomainGraph)

namespace TNLean.PEPS.AreaLaw.Scan

open Classical in
/-- The conclusions of Lemma 9.1 persist for a larger common constant, a larger logarithmic
power once `log n ≥ 1`, and a smaller sampling constant. -/
theorem HistoryFacts.mono {X : ScannerExponents} {n : ℕ} {C Cl c C' Cl' c' : ℝ}
    {ι Θ : Type} [Fintype ι] [MeasurableSpace Θ] {round : Fin (X.rounds n) → ScanRound ι Θ}
    (H : HistoryFacts X n C Cl c round) (hC0 : 0 ≤ C) (hC : C ≤ C') (hCl : Cl ≤ Cl')
    (hc : c' ≤ c) (hlog : 1 ≤ Real.log n) :
    HistoryFacts X n C' Cl' c' round := by
  have hL : Real.log n ^ Cl ≤ Real.log n ^ Cl' := Real.rpow_le_rpow_of_exponent_le hlog hCl
  have hL0 : 0 ≤ Real.log n ^ Cl := Real.rpow_nonneg (zero_le_one.trans hlog) _
  have hlogC : C * Real.log n ^ Cl ≤ C' * Real.log n ^ Cl' :=
    mul_le_mul hC hL hL0 (hC0.trans hC)
  refine
    { w_nonneg := H.w_nonneg
      q_nonneg := H.q_nonneg
      sum_w := H.sum_w
      sum_q := H.sum_q
      splitWeight_le := fun r p hp i ↦ (H.splitWeight_le r p hp i).trans (by gcongr)
      card_splitOld_le := fun r h ↦ (H.card_splitOld_le r h).trans (by gcongr)
      card_splitNew_le := fun r h c ↦ (H.card_splitNew_le r h c).trans (by gcongr)
      badWeight_le := H.badWeight_le
      sampling := fun r hr h hg θ ↦ le_trans (mul_le_mul_of_nonneg_right
        (by gcongr) (Finset.sum_nonneg fun i _ ↦ by
          split_ifs
          · exact H.etaOld_nonneg r i h θ
          · exact le_rfl)) (H.sampling r hr h hg θ)
      etaOld_nonneg := H.etaOld_nonneg
      etaOld_le := fun r i h θ ↦ (H.etaOld_le r i h θ).trans hlogC
      etaNew_nonneg := H.etaNew_nonneg
      etaNew_le := fun r i h c θ ↦ (H.etaNew_le r i h c θ).trans hlogC
      measurable_etaOld := H.measurable_etaOld
      measurable_etaNew := H.measurable_etaNew
      choiceGain_nonneg := H.choiceGain_nonneg
      measurable_choiceGain := H.measurable_choiceGain
      choiceGain_le := fun r h θ ↦ (H.choiceGain_le r h θ).trans (by
        rw [mul_right_comm C, mul_right_comm C']
        exact mul_le_mul_of_nonneg_right hlogC (Nat.cast_nonneg _)) }

namespace CollarScan

open SpectralFilter

/-- **Proposition 9.2 for the actual scan of one physical system**, from the conclusions of
Propositions 7.4 and 8.1. Fix scanner exponents, an interaction range `R`, an interaction
bound `J ≥ 0`, a gap `Δ > 0` and a target-size coefficient `C_T ≥ 0`, and put
`g = Δ / max(1, J(‖f‖₁ + 1))`. There is a truncation coefficient `C_tr`, and for every local
dimension `q` there are thresholds `C₀`, `c₀ > 0` and a charge-list constant `C₁ > 0`, such that
for all scanner constants `κ` with dimension `q`, gap `g`, `κ.C ≥ C₀`, `κ.C_l ≥ 4` and
`κ.c ≤ c₀`, there are constants for which, for all sufficiently large `n`, the following holds.
Every gapped physical system at scale `n` with a collar scan at the source scales
(`scanner:scales`) with `r₀ = ⌈C_tr log² n⌉`, under the test geometry
(`scanner:test-geometry`) and the entropy inputs (`scanner:entropy-input`), has one ground
vector `Ωt` of the truncated Hamiltonian, with gap `g/2`, satisfying the marginal moment bound
of Lemma 3.1 at every region, and a `ScanTruncation` built from it (its entropies, trace
distance, typical mass and typical dimension are those of `Ω` and `Ωt`, and its marginal-tail
parameter bounds the cut parameter of every status region), such that for every auxiliary
dimensions, total weight `W ≥ 1`, and replica vectors `pre`,
whenever the actual rounds (with per-band weight `a = W/K`) satisfy the conclusions `ScanInputs`
of Propositions 7.4 and 8.1 for `W` and the same truncation, the conclusions of Proposition 9.2
hold: the comparator budgets, and for every `k ≥ 1` a charge round and a common parameter
`p_k ∈ [ε/2, ε]` with the selected-density and defect-energy bounds.

Source: `08-scanner.tex`, Proposition 9.2, lines 349–533. -/
theorem scanner_estimate_actualScan (X : ScannerExponents) (R : ℕ) {J Δ CT : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCT : 0 ≤ CT) :
    ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (q : ℕ) [NeZero q], ∃ C₀ c₀ C₁ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧ 0 < C₁ ∧
      ∀ κ : ScanConstants, κ.q = q → κ.g = Δ / positiveNormalization 1 (Δ / 2) J →
      C₀ ≤ κ.C → 4 ≤ κ.Cl → κ.c ≤ c₀ →
      ∃ Cb Clb C Cl Cδ : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
        (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
            (S : CollarScan ↥Λ (AdmissibleSupport Λ R))
        (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
        ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        S.graph = planeDomainGraph Λ → S.depth = (fun x ↦ ambientDepth T hT x.val) →
        (∀ i, S.anchor i ∈ i.val) →
        S.n = n → S.m = X.m n → S.K = X.K n → S.D = X.D n →
        S.r₀ = ⌈Ctr * Real.log (n : ℝ) ^ 2⌉₊ → S.C₁ = C₁ →
        (T.card : ℝ) ≤ CT * (n : ℝ) ^ 2 →
        (∀ d : ℕ, 1 ≤ d → d ≤ X.L n →
          (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
        (∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ S.A,
          ((2 * X.L n + 10 * S.r₀ : ℕ) : ℤ) < (supDist t z : ℤ)) →
        ManyBody.regionEntropy Ω (S.target T) ≤ κ.Ce * (n : ℝ) ^ (1 + X.e) →
        (∀ j ≤ X.L n, ManyBody.regionEntropy Ω (S.shell T j) ≤
          κ.Ce * (n * (X.L n : ℝ) ^ X.e + n)) →
        let B : Finset ↥Λ → ℝ :=
          fun Y ↦ ManyBody.cutLogBudget
            (fun i ↦ designatedSupport S.graph (S.truncationSet (X.L n)) S.r₀ (S.anchor i))
            (fun _ ↦ q) Y
        ∃ (e : ℝ) (Ωt : EuclideanSpace ℂ (↥Λ → Fin q)),
          (‖Ωt‖ = 1 ∧ IsGapped (∑ i, S.truncatedEnergyTerm h Ω J Δ (X.L n) i) e (κ.g / 2) ∧
            groundSpace (∑ i, S.truncatedEnergyTerm h Ω J Δ (X.L n) i) e = Submodule.span ℂ {Ωt}) ∧
          (∀ (Y : Finset ↥Λ) (u : ℝ),
            |u| ≤ Entropy.tailRadius (2 / κ.g) (B Y) →
            Real.log (Entropy.surprisalMoment
              (ManyBody.regionState_isHermitian Y Ωt).eigenvalues u) ≤
              u * ManyBody.regionEntropy Ωt Y + 512 * Real.exp 1 * (2 / κ.g) * B Y * u ^ 2) ∧
          ∃ Tr : ScanTruncation X κ n,
            Tr.E0 = e ∧ Tr.gap = κ.g / 2 ∧
            Tr.SX = ManyBody.regionEntropy Ω (S.target T) ∧
            Tr.SXt = ManyBody.regionEntropy Ωt (S.target T) ∧
            Tr.SQ = (fun j ↦ ManyBody.regionEntropy Ω (S.shell T j)) ∧
            Tr.SQt = (fun j ↦ ManyBody.regionEntropy Ωt (S.shell T j)) ∧
            Tr.traceDist = Matrix.traceDistance
              (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ∧
            Tr.z = (ManyBody.regionState_isHermitian (S.target T) Ωt).spectralRestrictionMass
              (Entropy.typicalSet (ManyBody.regionState_isHermitian (S.target T) Ωt).eigenvalues
                (ManyBody.regionEntropy Ωt (S.target T)) Tr.width) ∧
            Tr.dstar = (Entropy.typicalSet
              (ManyBody.regionState_isHermitian (S.target T) Ωt).eigenvalues
                (ManyBody.regionEntropy Ωt (S.target T)) Tr.width).card ∧
            (∀ (k : ℕ) (hist : History S.K S.m S.M k) (band : Fin S.K),
              (k ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band), B Q ≤ Tr.Bmarg) ∧
              (k + 1 ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                  B Q ≤ Tr.Bmarg)) ∧
            ∀ (hm : 0 < S.m) (hM : 0 < S.M) (aux : Bool → ℕ) [∀ b, NeZero (aux b)]
              (W : ℝ), 1 ≤ W → ∀
              (pre : (k : ℕ) →
                Config k (fun v ↦ Fin (augmentedDimensions (V := ↥Λ) q aux v)) → ℂ),
              let round : Fin (X.rounds n) → ScanRound (AdmissibleSupport Λ R)
                  (CoherentSphere (∀ v, Fin ((augmentedDimensions (V := ↥Λ) q aux) v))) :=
                fun r ↦ S.actualScanRound hm hM (augmentedDimensions (V := ↥Λ) q aux)
                  (S.actualEnergyTerms h Ω J Δ (X.L n) aux) (X.a W n) pre r.val
              ∀ I : ScanInputs X κ n Tr round W,
                (I.Bsh ≤ Cb * (n * (X.L n : ℝ) ^ X.e + n) ∧ I.Bexc ≤ Cb * n * X.D n ∧
                  Tr.Bmarg ≤ Cb * n * X.D n * Real.log n ^ Clb) ∧
                ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k, 1 ≤ k →
                  ∃ r ∈ X.chargeRounds n, ∃ p ∈ Icc (X.eps n / 2) (X.eps n),
                    (round r).chargeDefect k p / (X.K n * n * X.D n) ≤
                        X.delta W Cδ κ.Cl n + ρ k ∧
                    ((round r).meanEnergy k p - Tr.E0) / Tr.gap ≤
                      C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
                          (X.delta W Cδ κ.Cl n ^ (1 / 8 : ℝ) + X.eps n +
                            (n : ℝ) ^ (-100 : ℝ)) +
                        C * (n : ℝ) ^ (-1000 : ℝ) + ρ k := by
  obtain ⟨Ctr, hCtr, htrunc⟩ := exists_scanTruncation X R hJ hΔ hCT
  refine ⟨Ctr, hCtr, ?_⟩
  intro q _
  have hq : 1 ≤ q := NeZero.pos q
  obtain ⟨C₀, hT⟩ := htrunc q
  obtain ⟨Ch, ch, C₁, hCh, hch, hC₁, hhist⟩ :=
    exists_historyFacts_actualScanRound (Ctr := Ctr) (CT := CT) X R hq hCtr hCT
  refine ⟨max (max C₀ Ch) 1, ch, C₁, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hch, hC₁,
    ?_⟩
  intro κ hκq hκg hκC hκCl hκc
  obtain ⟨Cb, Clb, C, Cl, Cδ, hscan⟩ := scanner_estimate X κ
  refine ⟨Cb, Clb, C, Cl, Cδ, ?_⟩
  filter_upwards [hT κ hκq hκg (((le_max_left _ _).trans (le_max_left _ _)).trans hκC), hhist,
    hscan,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n htr hH hS hlog
  intro Λ T _ hT h hh hhJ S E₀ Ω hΩ hgap hspan hgraph hdepth hanchor hSn hSm hSK hSD hSr
      hSC hsize hrows
      hclear
    hinX hinQ
  obtain ⟨e, Ωt, htrgs, hmom, Tr, hE0, hgap, hSX, hSXt, hSQ, hSQt, htd, hz, hdstar, hstat⟩ :=
    htr Λ T hT h hh hhJ S E₀ Ω hΩ hgap hspan hgraph hdepth hanchor hSn hSm hSK hSD hSr
        hsize hrows hclear
      hinX hinQ
  refine ⟨e, Ωt, htrgs, hmom, Tr, hE0, hgap, hSX, hSXt, hSQ, hSQt, htd, hz, hdstar, hstat, ?_⟩
  intro hm hM aux _ W hW pre round I
  have hHist := hH Λ T hT S hm hM (augmentedDimensions (V := ↥Λ) q aux)
    (S.actualEnergyTerms h Ω J Δ (X.L n) aux) (X.a W n) pre (fun _ ↦ rfl) (fun _ ↦ rfl)
    hSn hSm hSK hSD hSr hSC hsize hgraph hdepth hanchor hrows hclear
  let SD : ScanData X κ n :=
    { toScanTruncation := Tr
      ι := AdmissibleSupport Λ R
      Θ := CoherentSphere (∀ v, Fin ((augmentedDimensions (V := ↥Λ) q aux) v))
      round := round
      W := W
      one_le_W := hW
      histories := hHist.mono hCh (((le_max_right _ _).trans (le_max_left _ _)).trans hκC)
        hκCl hκc hlog
      inputs := I }
  exact hS SD

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
