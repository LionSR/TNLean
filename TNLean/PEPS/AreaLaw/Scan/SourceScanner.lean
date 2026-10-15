/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalScanner
import TNLean.PEPS.AreaLaw.Scan.AugmentedEnergyCoordinates
import QICLean.Representation.ReplicaPrevector

/-!
# The scanner estimate with the source hypotheses

This module states Proposition 9.2 (`prop:scanner`) of the area-law manuscript with exactly
the hypotheses of the source, as the proposition `CollarScan.ScannerStatement`, and proves it
from the conclusions of Propositions 7.4 and 8.1 for the actual rounds of the scan
(`CollarScan.ScanInputsSupply`).

The hypotheses of the statement are those of the source:

* the exponents `0 < ℓ < 1`, `0 < κ < μ < 1 - ℓ`, `0 < e < 1` with `κ ≤ e`, and `ν > 0`
  (`ScannerExponents`; `08-scanner.tex`, lines 41, 351–352 and 358);
* the local dimension `q ≥ 2`, the standing assumption of `01-preliminaries.tex`, line 121;
* a gapped physical system and a collar scan at the scales `scanner:scales`
  (lines 32–41), with `r₀ = ⌈C log² n⌉` (line 49) and the charge list of lines 127–130;
* the test geometry `scanner:test-geometry` (lines 43–48), with `X = A ∩ T` nonempty (line 24);
* the entropy inputs `scanner:entropy-input` for the original ground vector (lines 353–357);
* `a r₀²` sufficiently small (line 359).

Its conclusion is the source's: the truncated ground vector `Ω̃` of Proposition 4.5, the
auxiliary systems of dimension `d_*` (the typical window of width `n^{3/5}`) and a label
sequence for which the vectors `pre_k` of `comparator:prevector` are nonzero; the comparator
parameters with `B_sh ≤ C(nL^e + n)`, `B_exc ≤ CnD` and `𝓑 ≤ CnD(log n)^C`; and, for every
sufficiently large replica count `k`, a charge round and a common parameter
`p_k ∈ [ε/2, ε]` satisfying the defect-energy bound `scanner:energy-output`
(lines 361–384), with a remainder `o_k(1)` uniform over the selected round and parameter.

**Reading of the constants:** in the conclusions, the source writes `C_e` for constants that
may depend on the input constant `C_e` (line 396). The literal input constant cannot bound
`B_sh`, since a partial last depth row adds `n log q` (line 404); the statement therefore
takes the coefficients of `δ_n` and of `B_sh` existentially, like every other constant.

## Main definitions

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.ScannerHypotheses`: the source hypotheses on one
  physical system and one collar scan at scale `n`.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.scanPrevector`: the vectors `pre_k` of
  `comparator:prevector` in scanner coordinates.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.ScannerStatement`: Proposition 9.2 with the source
  hypotheses.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.ScanInputsSupply`: the conclusions of
  Propositions 7.4 and 8.1 for the actual rounds of every such scan.

## Main results

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.scannerStatement_of_scanInputsSupply`: Proposition 9.2
  holds once the conclusions of Propositions 7.4 and 8.1 hold for the actual rounds.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Proposition 9.2 (`prop:scanner`), `08-scanner.tex`, lines 349–397, proof lines 399–533,
  with the scales and test geometry of lines 21–59; Proposition 8.1 (`prop:comparators`),
  `07-comparators.tex`, lines 125–214. Source revision:
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Independently formalized from the
  manuscript; no upstream Lean proof text is reused.
-/

open Filter Topology Set
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

namespace CollarScan

open SpectralFilter

/-- **The source hypotheses of Proposition 9.2 at scale `n`.** A gapped ground vector `Ω`
of a Hamiltonian `h` on `Λ` with gap `Δ`; a collar scan `S` of the target `T` at the scales
`scanner:scales` (`08-scanner.tex`, lines 32–41), with the domain graph, ambient sup-norm
depth, anchors in their supports, `r₀ = ⌈C_tr log² n⌉` (line 49) and charge-list constant
`C₁` (lines 127–130); the test geometry `scanner:test-geometry` (lines 43–48); and the entropy
inputs `scanner:entropy-input` with constant `C_e` (lines 353–357). -/
structure ScannerHypotheses (X : ScannerExponents) (R : ℕ) (J Δ CT Ctr C₁ Ce : ℝ) (n : ℕ)
    {q : ℕ} (Λ T : Finset (ℤ × ℤ)) (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
    (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ) (Ω : StateSpace Λ q) :
    Prop where
  /-- `Ω` is a ground vector of `h` with gap `Δ`. -/
  groundState : IsGappedGroundState Λ q h.operator E₀ Ω Δ
  /-- Interaction supports use the graph metric of `Λ` (lines 15–16). -/
  graph_eq : S.graph = domainGraph Λ
  /-- Depth is the ambient sup-norm distance to the target (lines 14–15). -/
  depth_eq : S.depth = fun x ↦ ambientDepth T hT x.val
  /-- Every designated support contains its anchor. -/
  anchor_mem : ∀ i, S.anchor i ∈ i.val
  /-- `n` padded slots per depth row (line 87). -/
  n_eq : S.n = n
  /-- `m = ⌊n^μ⌋` (line 35). -/
  m_eq : S.m = X.m n
  /-- `K = ⌊L/(8m)⌋` (line 36). -/
  K_eq : S.K = X.K n
  /-- `D = ⌈n^κ⌉` (line 37). -/
  D_eq : S.D = X.D n
  /-- `r₀ = ⌈C log² n⌉` (line 49). -/
  r₀_eq : S.r₀ = ⌈Ctr * Real.log (n : ℝ) ^ 2⌉₊
  /-- The charge-list constant (lines 127–130). -/
  C₁_eq : S.C₁ = C₁
  /-- `|T| ≤ C n²` (line 46). -/
  card_le : (T.card : ℝ) ≤ CT * (n : ℝ) ^ 2
  /-- `|T_j \ T_{j-1}| ≤ n` for `1 ≤ j ≤ L` (line 46). -/
  rows_le : ∀ d : ℕ, 1 ≤ d → d ≤ X.L n →
    (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n
  /-- `dist_∞(T, Z) > 2L + 10 r₀` (line 46). -/
  clearance : ∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
    ((2 * X.L n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z
  /-- `S_Ω(X) ≤ C_e n^{1+e}` (line 355). -/
  entropy_target : regionalEntropy Λ q Ω (S.target T) ≤ Ce * (n : ℝ) ^ (1 + X.e)
  /-- `S_Ω(Q_j) ≤ C_e(nL^e + n)` for `0 ≤ j ≤ L` (line 356). -/
  entropy_shell : ∀ j ≤ X.L n,
    regionalEntropy Λ q Ω (S.shell T j) ≤ Ce * (n * (X.L n : ℝ) ^ X.e + n)

/-- The typical Schmidt set of the target for `Ω̃` with width `n^{3/5}`
(`comparator:typical-set`, `07-comparators.tex`, lines 37–47; `08-scanner.tex`, line 362). -/
def typicalWindow {Λ : Finset (ℤ × ℤ)} {I : Type*} (S : CollarScan (Site Λ) I) (q : ℕ)
    (Ωt : StateSpace Λ q) (T : Finset (ℤ × ℤ)) (n : ℕ) :=
  Entropy.typicalSet (reducedState_isHermitian Λ q Ωt (S.target T)).eigenvalues
    (regionalEntropy Λ q Ωt (S.target T)) ((n : ℝ) ^ (3 / 5 : ℝ))

/-- The vectors `pre_k = π_R^{λ_k}(Ω̃ ⊗ Bell_{CR})^{⊗k}` of `comparator:prevector`
(`07-comparators.tex`, lines 130–140), with auxiliary systems of dimension `d`, in the
coordinates of the scan. -/
def scanPrevector {Λ : Finset (ℤ × ℤ)} (q d : ℕ) (Ωt : StateSpace Λ q)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (k : ℕ) :
    Config k (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q (fun _ ↦ d) v)) → ℂ :=
  replicaPrevector (WithLp.ofLp Ωt) d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k

open Classical in
/-- **Proposition 9.2 with the source hypotheses** (`prop:scanner`, `08-scanner.tex`,
lines 349–397). Fix the exponents `X`, an interaction range `R`, an interaction bound `J`, a
gap `Δ` and a target-size coefficient `C_T`, and put `g = Δ / max(1, J(‖f‖₁ + 1))`. There is
a truncation coefficient `C_tr` such that for every local dimension `q ≥ 2` and entropy-input
constant `C_e` there are constants, a charge-list constant `C₁ > 0` and a smallness threshold
`c_a > 0` with the following property for all sufficiently large `n`.

Let a gapped physical system and a collar scan satisfy the source hypotheses
(`ScannerHypotheses`). Then the truncated Hamiltonian of Proposition 4.5 has a ground vector
`Ω̃` with energy `Ẽ₀` and gap `g/2`; its typical window `E` of width `n^{3/5}` is nonempty;
and there is a label sequence `λ_k` for which the vectors `pre_k` of `comparator:prevector`,
with auxiliary dimension `d_* = |E|`, are nonzero for `k ≥ 1`. For every total weight
`W ≥ 1` with `a r₀² ≤ c_a`, the actual rounds of the scan built from `pre` satisfy:

* (comparator parameters, lines 388–392) there are `B_sh ≤ C_b(nL^e + n)`,
  `B_exc ≤ C_b nD` and `𝓑 ≤ C_b nD(log n)^{C_{lb}}`, where `𝓑` bounds the marginal-tail
  parameter of every status cut and `Ω̃` satisfies the marginal moment bound of Lemma 3.1, and
  where `B_sh`, `B_exc` give the rough upper comparison `comparator:rough-upper` at the last
  endpoint of the scan with a remainder `o_k(1)`;
* (energy, `scanner:energy-output`) there is a remainder `ρ_k → 0` such that for every
  sufficiently large `k` some charge round and some `p_k ∈ [ε/2, ε]` satisfy
  `E_def,k ≤ C n^ℓ D² W² (log n)^{C_l} (δ_n^{1/8} + ε + n^{-100}) + C n^{-1000} + ρ_k`, with
  `δ_n = C_δ ε^{-1}(n^{e-μ} + a^{1/4}(log n)^{C_{lδ}})`.

The defect energy divides by the lower bound `g/2` of the gap `g̃` (line 54). -/
def ScannerStatement (X : ScannerExponents) (R : ℕ) (J Δ CT : ℝ) : Prop :=
  ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ Ce : ℝ,
    ∃ C₁ Cb Clb C Cl Cδ Clδ ca : ℝ, 0 < C₁ ∧ 0 < ca ∧ ∀ᶠ n : ℕ in atTop,
    ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
      (h : LocalHamiltonian Λ q R J) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
      (E₀ : ℝ) (Ω : StateSpace Λ q),
      ScannerHypotheses X R J Δ CT Ctr C₁ Ce n Λ T hT h S E₀ Ω →
      let g : ℝ := Δ / positiveNormalization 1 (Δ / 2) J
      let B : Finset (Site Λ) → ℝ :=
        fun Y ↦ cutBudget q S.graph (S.truncationSet (X.L n)) S.r₀ S.anchor Y
      ∃ (e : ℝ) (Ωt : StateSpace Λ q),
        IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ (X.L n) i) e Ωt (g / 2) ∧
        let E := S.typicalWindow q Ωt T n
        let z := (reducedState_isHermitian Λ q Ωt (S.target T)).spectralRestrictionMass E
        ∃ (hm : 0 < S.m) (hM : 0 < S.M) (hd : 0 < E.card),
        haveI : NeZero E.card := ⟨hd.ne'⟩
        ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
          (∀ k, 0 < k → scanPrevector q E.card Ωt ell k ≠ 0) ∧
          ∀ W : ℝ, 1 ≤ W → X.a W n * (S.r₀ : ℝ) ^ 2 ≤ ca →
            let round : Fin (X.rounds n) → ScanRound (AdmissibleSupport Λ R)
                (CoherentSphere
                  (SiteConfig (augmentedDimensions (V := Site Λ) q (fun _ ↦ E.card)))) :=
              fun r ↦ S.actualScanRound hm hM
                (augmentedDimensions (V := Site Λ) q (fun _ ↦ E.card))
                (S.actualEnergyTerms h Ω Δ (X.L n) (fun _ ↦ E.card)) (X.a W n)
                (scanPrevector q E.card Ωt ell) r.val
            (∃ Bsh Bexc Bmarg : ℝ,
              Bsh ≤ Cb * (n * (X.L n : ℝ) ^ X.e + n) ∧ Bexc ≤ Cb * n * X.D n ∧
              Bmarg ≤ Cb * n * X.D n * Real.log n ^ Clb ∧
              (∀ (Y : Finset (Site Λ)) (u : ℝ),
                |u| ≤ Entropy.tailRadius (2 / g) (B Y) →
                Real.log (Entropy.surprisalMoment
                  (reducedState_isHermitian Λ q Ωt Y).eigenvalues u) ≤
                  u * regionalEntropy Λ q Ωt Y + 512 * Real.exp 1 * (2 / g) * B Y * u ^ 2) ∧
              (∀ (k : ℕ) (hist : History S.K S.m S.M k) (band : Fin S.K),
                (k ≤ S.n * S.m →
                  ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band), B Q ≤ Bmarg) ∧
                (k + 1 ≤ S.n * S.m →
                  ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                    B Q ≤ Bmarg)) ∧
              ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
                ∀ r : Fin (X.rounds n), r.val + 1 = X.rounds n →
                  -(round r).logNormSq k 1 / k ≤
                    2 * Real.log E.card - Real.log z +
                      2 * (1 / 4) * W * (2 * Bsh / z + 2 * Bexc) + ρ k) ∧
            ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
              ∃ r ∈ X.chargeRounds n, ∃ p ∈ Icc (X.eps n / 2) (X.eps n),
                ((round r).meanEnergy k p - e) / (g / 2) ≤
                  C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
                      (X.delta W Cδ Clδ n ^ (1 / 8 : ℝ) + X.eps n +
                        (n : ℝ) ^ (-100 : ℝ)) +
                    C * (n : ℝ) ^ (-1000 : ℝ) + ρ k

open Classical in
/-- **The conclusions of Propositions 7.4 and 8.1 for the actual scan.** For every
truncation coefficient, local dimension `q ≥ 2`, charge-list constant and entropy-input
constant there are thresholds for the common constant and logarithmic power and a smallness
threshold `c_a > 0` such that, for all scanner constants above the thresholds and all
sufficiently large `n`, the following holds for every physical system and collar scan under
the source hypotheses. Let `Ω̃` be a ground vector of the truncated Hamiltonian with gap
`g/2` satisfying the marginal moment bound of Lemma 3.1, and let `Tr` record its truncation
inputs, with marginal-tail parameter bounding the cut parameter of every status region. Then there is a label sequence for which the vectors `pre_k` of
`comparator:prevector` are nonzero for `k ≥ 1` (`07-comparators.tex`, lines 130–140), and for
every total weight `W ≥ 1` with `a r₀² ≤ c_a` the actual rounds built from `pre` satisfy the
conclusions `ScanInputs` of Proposition 7.4 (`06-transport.tex`, lines 377–433) and
Proposition 8.1 (`07-comparators.tex`, lines 125–214). -/
def ScanInputsSupply (X : ScannerExponents) (R : ℕ) (J Δ CT : ℝ) : Prop :=
  ∀ Ctr : ℝ, 0 < Ctr → ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ C₁ : ℝ, 0 < C₁ → ∀ Ce : ℝ,
    ∃ C₀ Cl₀ ca : ℝ, 0 < ca ∧ ∀ κ : ScanConstants, κ.q = q →
      κ.g = Δ / positiveNormalization 1 (Δ / 2) J → κ.Ce = Ce → C₀ ≤ κ.C → Cl₀ ≤ κ.Cl →
      ∀ᶠ n : ℕ in atTop,
      ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
        (h : LocalHamiltonian Λ q R J) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
        (E₀ : ℝ) (Ω : StateSpace Λ q),
        ScannerHypotheses X R J Δ CT Ctr C₁ Ce n Λ T hT h S E₀ Ω →
        let B : Finset (Site Λ) → ℝ :=
          fun Y ↦ cutBudget q S.graph (S.truncationSet (X.L n)) S.r₀ S.anchor Y
        ∀ (e : ℝ) (Ωt : StateSpace Λ q),
          IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ (X.L n) i) e Ωt
            (κ.g / 2) →
          (∀ (Y : Finset (Site Λ)) (u : ℝ),
            |u| ≤ Entropy.tailRadius (2 / κ.g) (B Y) →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Y).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Y + 512 * Real.exp 1 * (2 / κ.g) * B Y * u ^ 2) →
          ∀ Tr : ScanTruncation X κ n,
            Tr.E0 = e → Tr.gap = κ.g / 2 →
            Tr.SX = regionalEntropy Λ q Ω (S.target T) →
            Tr.SXt = regionalEntropy Λ q Ωt (S.target T) →
            Tr.SQ = (fun j ↦ regionalEntropy Λ q Ω (S.shell T j)) →
            Tr.SQt = (fun j ↦ regionalEntropy Λ q Ωt (S.shell T j)) →
            Tr.traceDist = Matrix.traceDistance
              (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
              (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) →
            Tr.z = (reducedState_isHermitian Λ q Ωt (S.target T)).spectralRestrictionMass
              (S.typicalWindow q Ωt T n) →
            Tr.dstar = (S.typicalWindow q Ωt T n).card →
            (∀ (k : ℕ) (hist : History S.K S.m S.M k) (band : Fin S.K),
              (k ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band), B Q ≤ Tr.Bmarg) ∧
              (k + 1 ≤ S.n * S.m →
                ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                  B Q ≤ Tr.Bmarg)) →
            ∀ (hm : 0 < S.m) (hM : 0 < S.M) (hd : 0 < (S.typicalWindow q Ωt T n).card),
            haveI : NeZero (S.typicalWindow q Ωt T n).card := ⟨hd.ne'⟩
            ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
              (∀ k, 0 < k → scanPrevector q (S.typicalWindow q Ωt T n).card Ωt ell k ≠ 0) ∧
              ∀ W : ℝ, 1 ≤ W → X.a W n * (S.r₀ : ℝ) ^ 2 ≤ ca →
                Nonempty (ScanInputs X κ n Tr
                  (fun r ↦ S.actualScanRound hm hM
                    (augmentedDimensions (V := Site Λ) q
                      (fun _ ↦ (S.typicalWindow q Ωt T n).card))
                    (S.actualEnergyTerms h Ω Δ (X.L n)
                      (fun _ ↦ (S.typicalWindow q Ωt T n).card)) (X.a W n)
                    (scanPrevector q (S.typicalWindow q Ωt T n).card Ωt ell) r.val) W)

/-- **Proposition 9.2 from the conclusions of Propositions 7.4 and 8.1.** Once the actual
rounds of every collar scan under the source hypotheses satisfy the conclusions of
Propositions 7.4 and 8.1 (`ScanInputsSupply`), the scanner estimate holds with exactly the
source hypotheses (`ScannerStatement`).

Source: `08-scanner.tex`, Proposition 9.2, lines 349–533. -/
theorem scannerStatement_of_scanInputsSupply (X : ScannerExponents) (R : ℕ) {J Δ CT : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCT : 0 ≤ CT) (hI : ScanInputsSupply X R J Δ CT) :
    ScannerStatement X R J Δ CT := by
  obtain ⟨Ctr, hCtr, H⟩ := scanner_estimate_actualScan X R hJ hΔ hCT
  refine ⟨Ctr, hCtr, fun q _ hq Ce ↦ ?_⟩
  obtain ⟨C₀, c₀, C₁, hC₀, hc₀, hC₁, H⟩ := H q
  obtain ⟨C₀', Cl₀', ca, hca, hsup⟩ := hI Ctr hCtr q hq C₁ hC₁ (max Ce 1)
  let κ : ScanConstants :=
    { C := max (max C₀ C₀') 1
      Cl := max 4 Cl₀'
      c := c₀
      Ce := max Ce 1
      q := q
      g := Δ / positiveNormalization 1 (Δ / 2) J
      one_le_C := le_max_right _ _
      Cl_nonneg := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)
      c_pos := hc₀
      Ce_pos := one_pos.trans_le (le_max_right _ _)
      two_le_q := hq
      g_pos := div_pos hΔ (positiveNormalization_pos 1 _ J) }
  obtain ⟨Cb, Clb, C, Cl, Cδ, H⟩ := H κ rfl rfl ((le_max_left _ _).trans (le_max_left _ _))
    (le_max_left _ _) le_rfl
  refine ⟨C₁, Cb, Clb, C, Cl, Cδ, κ.Cl, ca, hC₁, hca, ?_⟩
  filter_upwards [H, hsup κ rfl rfl rfl ((le_max_right _ _).trans (le_max_left _ _))
    (le_max_right _ _), eventually_ge_atTop 1] with n hn hs hn1
  intro Λ T _ hT h S E₀ Ω hyp
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (1 + X.e) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hshell : (0 : ℝ) ≤ n * (X.L n : ℝ) ^ X.e + n := by positivity
  have hinX : regionalEntropy Λ q Ω (S.target T) ≤ κ.Ce * (n : ℝ) ^ (1 + X.e) :=
    hyp.entropy_target.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
  have hinQ : ∀ j ≤ X.L n, regionalEntropy Λ q Ω (S.shell T j) ≤
      κ.Ce * (n * (X.L n : ℝ) ^ X.e + n) := fun j hj ↦
    (hyp.entropy_shell j hj).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hshell)
  have hyp' : ScannerHypotheses X R J Δ CT Ctr C₁ (max Ce 1) n Λ T hT h S E₀ Ω :=
    { hyp with
      entropy_target := hinX
      entropy_shell := hinQ }
  obtain ⟨e, Ωt, htrgs, hmom, Tr, hE0, hgap, hSX, hSXt, hSQ, hSQt, htd, hz, hdstar, hstat,
      hfin⟩ :=
    hn Λ T hT h S E₀ Ω hyp.groundState hyp.graph_eq hyp.depth_eq hyp.anchor_mem hyp.n_eq
      hyp.m_eq hyp.K_eq hyp.D_eq hyp.r₀_eq hyp.C₁_eq hyp.card_le hyp.rows_le hyp.clearance
      hinX hinQ
  rw [Tr.width_eq] at hz hdstar
  have hm : 0 < S.m := by
    rw [hyp.m_eq]
    exact Nat.floor_pos.mpr (Real.one_le_rpow (by exact_mod_cast hn1)
      (X.kappa_pos.trans X.kappa_lt_mu).le)
  have hM : 0 < S.M := by
    have hD : (0 : ℝ) < S.D := by
      rw [hyp.D_eq]
      exact_mod_cast Nat.ceil_pos.mpr
        (Real.rpow_pos_of_pos (by exact_mod_cast hn1) _)
    have hn0 : (0 : ℝ) < S.n := by rw [hyp.n_eq]; exact_mod_cast hn1
    exact Nat.ceil_pos.mpr (by rw [hyp.C₁_eq]; positivity)
  have hd : 0 < (S.typicalWindow q Ωt T n).card := by
    have := Tr.dstar_pos
    rw [hdstar] at this
    exact_mod_cast this
  have : NeZero (S.typicalWindow q Ωt T n).card := ⟨hd.ne'⟩
  obtain ⟨ell, hne, hW⟩ := hs Λ T hT h S E₀ Ω hyp' e Ωt htrgs hmom Tr hE0 hgap hSX hSXt hSQ
    hSQt htd hz hdstar hstat hm hM hd
  refine ⟨e, Ωt, htrgs, hm, hM, hd, ell, hne, fun W hW1 ha ↦ ?_⟩
  obtain ⟨I⟩ := hW W hW1 ha
  obtain ⟨⟨hBsh, hBexc, hBmarg⟩, ρ, hρ, hsel⟩ :=
    hfin hm hM (fun _ ↦ (S.typicalWindow q Ωt T n).card) W hW1
      (scanPrevector q (S.typicalWindow q Ωt T n).card Ωt ell) I
  refine ⟨⟨I.Bsh, I.Bexc, Tr.Bmarg, hBsh, hBexc, hBmarg, hmom, hstat, I.rem, I.tendsto_rem,
    eventually_atTop.mpr ⟨1, fun k hk r hr ↦ ?_⟩⟩, ρ, hρ, eventually_atTop.mpr ⟨1, fun k hk ↦ ?_⟩⟩
  · have := I.logNormSq_final r hr k hk
    rwa [hdstar, hz] at this
  · obtain ⟨r, hr, p, hp, -, hE⟩ := hsel k hk
    refine ⟨r, hr, p, hp, ?_⟩
    rwa [hE0, hgap] at hE

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
