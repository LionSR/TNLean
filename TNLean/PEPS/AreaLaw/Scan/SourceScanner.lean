/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PhysicalScanner
import TNLean.PEPS.AreaLaw.Scan.AugmentedEnergyCoordinates
import QICLean.Representation.ReplicaPrevector
import TNLean.PEPS.AreaLaw.Scan.SuppliedTargetNormAttachment
import TNLean.PEPS.AreaLaw.Scan.ActualRoughUpper
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedEnergy

/-!
# The scanner estimate and four norm comparisons

The scanner estimate constructs one truncated ground vector, one target typical set,
and one sequence of Schmidt--Bell labels before the total weight is chosen. For each
sufficiently large replica count, one charge round and one interpolation parameter
satisfy the selected-density and defect-energy bounds and all four norm comparisons.
The sharp comparisons retain their marginal smallness condition. The same truncated
vector retains its trace-distance estimate to the original vector, and every
positive-copy prevector retains its Euclidean norm bound by one.

The hypotheses are the admissible scanner exponents, the original gapped local
Hamiltonian, the rounded scan scales, the target geometry and the entropy bounds of
Proposition 9.2. The truncation coefficient is chosen before the local dimension
and entropy coefficient. All remaining uniform constants and the size threshold
are chosen before the finite physical system and the total weight. The state and
label sequence are fixed before the replica limit.

**Local fix (input and output entropy coefficients):** the input coefficient \(C_e\)
is retained in the original entropy hypotheses. The output coefficients of the
shell bound and selected-density bound may be enlarged after \(C_e\) is fixed.
In the proof, with \(C_e^{\prime}=\max\{C_e,1\}\), the shell bound is
\(C_e^{\prime}(nL^e+n)+n^{-247}\le(C_e^{\prime}+1)(nL^e+n)\).
The energy coefficient \(C\) and density coefficient \(C_\delta\) are positive.
The density coefficient may remain positive when \(C_e=0\).
This records the absorption of fixed factors and additive errors allowed by
the source's dependence of constants on \(C_e\); it does not establish the stronger
reading in which each output uses the identical numerical input coefficient.
See `docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

## Main definitions

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.ScannerHypotheses`: the physical, geometric,
  scale and entropy assumptions at one scan size.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.typicalWindow`: the target typical set at
  width \(n^{3/5}\).
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.scanPrevector`: the Schmidt--Bell replica
  vector in the scan coordinates.
* `TNLean.PEPS.AreaLaw.Scan.CollarScan.ScannerStatement`: the scanner conclusion
  with enlarged output coefficients and all four comparisons at the same point.

## Main result

* `TNLean.PEPS.AreaLaw.Scan.CollarScan.scannerStatement`: the scanner conclusion
  for the original gapped Hamiltonian under the stated geometry and entropy bounds.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Proposition 9.2 (`prop:scanner`), `08-scanner.tex`, lines 349–397 and proof
lines 399–533; scales and geometry, lines 21–59; Proposition 8.1
(`prop:comparators`), `07-comparators.tex`, lines 125–214. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Topology Set Matrix
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open TensorPower TensorPower.ReplicaTransport Entropy

noncomputable section

namespace TNLean.PEPS.AreaLaw.Scan

namespace CollarScan

open SpectralFilter ActualTerminals

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
  /-- `Ω` is a ground vector of `h` with gap `Δ`: the original ground vector of the standing
  setting (`01-preliminaries.tex`, lines 4–5), to which the entropy inputs refer
  (`08-scanner.tex`, lines 343–347). -/
  groundState : IsGappedGroundState Λ q h.operator E₀ Ω Δ
  /-- Interaction supports use the graph metric of `Λ` (lines 15–16). -/
  graph_eq : S.graph = domainGraph Λ
  /-- Depth is the ambient sup-norm distance to the target (lines 14–15). -/
  depth_eq : S.depth = fun x ↦ ambientDepth T hT x.val
  /-- Every designated support contains its anchor: `a_i ∈ X_i` (`03-quasilocal.tex`,
  line 15; `01-preliminaries.tex`, line 94). -/
  anchor_mem : ∀ i, S.anchor i ∈ i.val
  /-- The target `X = A ∩ T` is nonempty (line 23). -/
  target_nonempty : (S.target T).Nonempty
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

/-- The typical Schmidt set of the target for `Ωt` with width `n^{3/5}`
(`comparator:typical-set`, `07-comparators.tex`, lines 37–47; `08-scanner.tex`, line 362). -/
def typicalWindow {Λ : Finset (ℤ × ℤ)} {I : Type*} (S : CollarScan (Site Λ) I) (q : ℕ)
    (Ωt : StateSpace Λ q) (T : Finset (ℤ × ℤ)) (n : ℕ) :=
  Entropy.typicalSet (reducedState_isHermitian Λ q Ωt (S.target T)).eigenvalues
    (regionalEntropy Λ q Ωt (S.target T)) ((n : ℝ) ^ (3 / 5 : ℝ))

/-- The vectors `pre_k = π_R^{λ_k}(Ωt ⊗ Bell_{CR})^{⊗k}` of `comparator:prevector`
(`07-comparators.tex`, lines 130–140), with auxiliary systems of dimension `d`, in the
coordinates of the scan. -/
def scanPrevector {Λ : Finset (ℤ × ℤ)} (q d : ℕ) (Ωt : StateSpace Λ q)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (k : ℕ) :
    Config k (fun v ↦ Fin (augmentedDimensions (V := Site Λ) q (fun _ ↦ d) v)) → ℂ :=
  replicaPrevector (WithLp.ofLp Ωt) d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k

open Classical in
/-- The scanner conclusion with one truncated ground vector and label sequence,
chosen before the total weight, and one charge round and interpolation parameter
for the selected-density, defect-energy and four norm comparisons. The sharp
comparisons retain their marginal smallness condition. The truncation coefficient
precedes the local dimension; the output entropy coefficients may be enlarged as
specified in the module's local-fix note. The same typical window has mass
`0 < 1 - n⁻¹⁰⁰ ≤ z ≤ 1`, as in `08-scanner.tex`, lines 411–414.
The truncated vector retains the trace-distance bound used in lines 400–403,
and the same positive-copy prevectors have Euclidean norm at most one
(`07-comparators.tex`, lines 130–140).

Source: Proposition 9.2 (`prop:scanner`), `08-scanner.tex`, lines 349–397 and
399–533, with Proposition 8.1 (`prop:comparators`), `07-comparators.tex`,
lines 125–214, at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
def ScannerStatement (X : ScannerExponents) (R : ℕ) (J Δ CT : ℝ) : Prop :=
  ∃ Ctr : ℝ, 0 < Ctr ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ Ce : ℝ,
    ∃ C₁ Cb Clb C Cl Cδ Clδ ca : ℝ,
      0 < C₁ ∧ 0 < C ∧ 0 < Cδ ∧ 0 < ca ∧ ∀ᶠ n : ℕ in atTop,
    ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)] (hT : T.Nonempty)
      (h : LocalHamiltonian Λ q R J) (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
      (E₀ : ℝ) (Ω : StateSpace Λ q),
      ScannerHypotheses X R J Δ CT Ctr C₁ Ce n Λ T hT h S E₀ Ω →
      let g : ℝ := Δ / positiveNormalization 1 (Δ / 2) J
      let C₀ := 512 * Real.exp 1 * (2 / g)
      let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
      let B : Finset (Site Λ) → ℝ :=
        fun Y ↦ cutBudget q S.graph (S.truncationSet (X.L n)) S.r₀ S.anchor Y
      ∃ (e : ℝ) (Ωt : StateSpace Λ q),
        IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ (X.L n) i) e Ωt (g / 2) ∧
        0 ≤ e ∧ e ≤ (n : ℝ) ^ (-1000 : ℝ) ∧
        Matrix.traceDistance
            (Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))
            (Matrix.vecMulVec Ω.ofLp (star Ω.ofLp)) ≤
          Real.sqrt (2 * min ((n : ℝ) ^ (-1000 : ℝ)) (g / 4) / g) ∧
        let E := S.typicalWindow q Ωt T n
        let z := (reducedState_isHermitian Λ q Ωt (S.target T)).spectralRestrictionMass E
        0 < 1 - (n : ℝ) ^ (-100 : ℝ) ∧
        1 - (n : ℝ) ^ (-100 : ℝ) ≤ z ∧ 0 < z ∧ z ≤ 1 ∧
        ∃ (hm : 0 < S.m) (hM : 0 < S.M) (hd : 0 < E.card),
        haveI : NeZero E.card := ⟨hd.ne'⟩
        let d := E.card
        let β := fun _ : Site Λ ↦ Fin q
        let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (FiniteProduct.splitEquiv β (S.target T)) Ωt
        let ψ : FiniteProduct.Configuration β (S.target T)ᶜ × Fin d → ℂ := fun x ↦
          compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
        let Sent := _root_.vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
          (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
        ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
          (∀ k, 0 < k → scanPrevector q d Ωt ell k ≠ 0 ∧
            ‖WithLp.toLp 2 (scanPrevector q d Ωt ell k)‖ ≤ 1) ∧
          let dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
          let energy := S.actualEnergyTerms h Ω Δ (X.L n) (fun _ ↦ d)
          let pre := scanPrevector q d Ωt ell
          let σ := terminalPartition S (S.n * S.m)
          let Qpre := fun j band ↦ receiving (σ j band) false
          let Y := fun j band ↦ middle (σ j band)
          let gpre := fun j band ↦ FiniteProduct.entropy β Ωt (Qpre j band) +
            FiniteProduct.entropy β Ωt (Qpre j band ∪ Y j band)ᶜ -
              FiniteProduct.entropy β Ωt (Y j band)
          let gpost := fun j band ↦
            regionalEntropy Λ q Ωt (positiveNear S.depth (σ j band)) +
              regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j band)) -
                regionalEntropy Λ q Ωt (middle (σ j band))
          let gaps := (Finset.univ :
            Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
              (fun j ↦ gpre j.1 j.2)
          let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
          ∀ W : ℝ, 1 ≤ W → X.a W n * (S.r₀ : ℝ) ^ 2 ≤ ca →
            let a := X.a W n
            let round : Fin (X.rounds n) → ScanRound (AdmissibleSupport Λ R)
                (CoherentSphere (SiteConfig dims)) :=
              fun r ↦ S.actualScanRound hm hM dims energy a pre r.val
            ∃ Bsh Bexc Bmarg : ℝ,
              Bsh ≤ Cb * (n * (X.L n : ℝ) ^ X.e + n) ∧ Bexc ≤ Cb * n * X.D n ∧
              1 ≤ Bmarg ∧ Bmarg ≤ Cb * n * X.D n * Real.log n ^ Clb ∧
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
              (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
                ∀ r : Fin (X.rounds n), r.val + 1 = X.rounds n →
                  -(round r).logNormSq k 1 / k ≤
                    2 * Real.log d - Real.log z +
                      2 * (1 / 4) * W * (2 * Bsh / z + 2 * Bexc) + ρ k) ∧
              ∃ (ρ : ℕ → ℝ) (cRU cRL CfRL cSU cSL CfSL : ℝ),
                Tendsto ρ atTop (𝓝 0) ∧
                0 ≤ cRU ∧ 0 ≤ cRL ∧ 0 ≤ CfRL ∧ 0 ≤ cSU ∧ 0 ≤ cSL ∧ 0 ≤ CfSL ∧
                Tendsto (Real.bellOverlapRemainder d cRU S.K) atTop (𝓝 0) ∧
                Tendsto (roughLowerRemainderAtWeight S.K a cRL CfRL ell Sent)
                  atTop (𝓝 0) ∧
                Tendsto (Real.bellOverlapRemainder d cSU S.K) atTop (𝓝 0) ∧
                Tendsto (sharpLowerRemainder a cSL CfSL ell Sent) atTop (𝓝 0) ∧
                ∀ᶠ k : ℕ in atTop,
                  ∃ r ∈ X.chargeRounds n, ∃ s : Fin (S.n * S.m),
                    r.val = 2 * s.val + 1 ∧
                    ∃ p ∈ Icc (X.eps n / 2) (X.eps n),
                      let defect := ((round r).meanEnergy k p - e) / (g / 2)
                      let Nsq := Matrix.Transport.filteredNormSq
                        ((S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p) (pre k)
                      let tree :=
                        ((S.actualChargeData hm hM s.val).tree
                          (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
                            (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
                      (round r).chargeDefect k p / (X.K n * n * X.D n) ≤
                          X.delta W Cδ Clδ n + ρ k ∧
                      defect ≤
                        C * (n : ℝ) ^ X.ell * (X.D n : ℝ) ^ 2 * W ^ 2 * Real.log n ^ Cl *
                            (X.delta W Cδ Clδ n ^ (1 / 8 : ℝ) + X.eps n +
                              (n : ℝ) ^ (-100 : ℝ)) +
                          C * (n : ℝ) ^ (-1000 : ℝ) + ρ k ∧
                      0 < Nsq ∧ 0 ≤ defect ∧
                      -(round r).logNormSq k p / (k : ℝ) ≤
                        2 * Real.log d - Real.log z + W * (Bsh / z + Bexc) +
                          Real.bellOverlapRemainder d cRU S.K k ∧
                      (∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                        (W / 4) *
                            (4 * Sent - 6 * (τ * Real.log d + Real.binEntropy τ / a) -
                              3 * (defect / τ) * max 0 (2 * Sent)) -
                            roughLowerRemainderAtWeight S.K a cRL CfRL ell Sent k ≤
                              -(round r).logNormSq k p / (k : ℝ)) ∧
                      (a * Real.sqrt Bmarg ≤ min c₀ 1 / 10 →
                        -(round r).logNormSq k p / (k : ℝ) ≤
                          2 * Real.log d - Real.log z +
                            (a / 2) * (∑ band, ∑ j, tree.weight j * gpost j band) +
                              6 * (S.K : ℝ) * (C₀ * Bmarg) * a ^ 2 -
                                (S.K : ℝ) / 2 * Real.log z +
                                  Real.bellOverlapRemainder d cSU S.K k ∧
                        ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                          let sharpRate := fun band ↦ 2 * Sent +
                            (1 - τ) * (∑ j, tree.weight j * gpre j band) -
                              τ * (2 * Real.log d) - (3 + 1 / a) * Real.binEntropy τ -
                                25 * (C₀ * Bmarg) * a
                          (a / 2) * (∑ band,
                            (sharpRate band - defect / τ * max 0 (2 * Sent + gmax) -
                              sharpLowerRemainder a cSL CfSL ell Sent k)) ≤
                                -(round r).logNormSq k p / (k : ℝ))

/-- The scanner estimate with all four norm comparisons at one selected charge and parameter.
The truncation coefficient precedes the local dimension. The original entropy hypotheses are
retained, with the enlarged output coefficients specified in the module's local-fix note.

Source: Proposition 9.2 (`prop:scanner`), `08-scanner.tex`, lines 349–397 and 399–533,
and Proposition 8.1 (`prop:comparators`), `07-comparators.tex`, lines 125–214,
at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem scannerStatement (X : ScannerExponents) (R : ℕ) {J Δ CT : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hCT : 0 ≤ CT) : ScannerStatement X R J Δ CT := by
  obtain ⟨Ctr, hCtr, henergy⟩ :=
    exists_sourceTarget_selected_actualCharge_source_density_energy R hJ hΔ hCT
  refine ⟨Ctr, hCtr, fun q _ hq Ce ↦ ?_⟩
  let μ : ℕ := 2 ^ ((1 + 2 * R * (R + 1)) - 1)
  have hC₁ : 0 < 3 * (μ : ℝ) + 1 := by positivity
  obtain ⟨Ctarget, c, Cent, eent, Cen, een, hCtarget, hc, hchalf, henergy⟩ :=
    henergy q (by omega) (3 * (μ : ℝ) + 1) hC₁ μ
      (le_add_of_nonneg_right zero_le_one)
  obtain ⟨C, Cl, hC, hCl, henergy⟩ := henergy X
  obtain ⟨Cδ, Clδ, hCδ, hClδ, N, hN, henergy⟩ :=
    henergy (max Ce 1) (le_trans zero_le_one (le_max_right Ce 1))
  obtain ⟨CBnorm, hCBnorm, hnorm⟩ :=
    exists_suppliedTarget_actualCharge_norm_bounds (q := q) (by omega) R hCtr
  obtain ⟨CBcut, hCBcut, hbudget⟩ :=
    exists_statusMarginal_cutBudget_le_log (q := q) (by omega) R hCtr.le
  let Cb := max (max CBcut CBnorm) (max (max Ce 1 + 1) (1 + 3 * Real.log q))
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  obtain ⟨Ne, hprefix⟩ := eventually_atTop.mp
    (eventually_regionalEntropy_positiveDepthPrefix_le q (by omega)
      (Δ / positiveNormalization 1 (Δ / 2) J) (CT + 1) hg)
  refine ⟨3 * (μ : ℝ) + 1, Cb, 12, Cδ, Clδ, Cδ, Clδ, c, hC₁, hCδ, hCδ, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (max N Ne)] with n hn
  intro Λ T _ hT h S E₀ Ω hyp g C₀ c₀ B
  rcases hyp.n_eq with rfl
  have hprefix_eq_shell (j : ℕ) :
      positiveDepthPrefix S.A S.depth (j : ℤ) = S.shell T j := by
    simpa only [hyp.depth_eq, Int.toNat_natCast, Finset.mem_sdiff, CollarScan.shell] using
      (positiveDepthPrefix_eq_filter_ambientDilation hT S.A (j : ℤ))
  have htarget : regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ T) ≤
      max Ce 1 * (S.n : ℝ) ^ (1 + X.e) :=
    hyp.entropy_target.trans (mul_le_mul_of_nonneg_right (le_max_left Ce 1)
      (Real.rpow_nonneg (Nat.cast_nonneg S.n) _))
  have hsource : ∀ j : ℕ, j ≤ X.L S.n →
      regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
        max Ce 1 * ((S.n : ℝ) * (X.L S.n : ℝ) ^ X.e + S.n) := fun j hj ↦ by
    simpa only [hprefix_eq_shell j] using
      (hyp.entropy_shell j hj).trans
        (mul_le_mul_of_nonneg_right (le_max_left Ce 1) (by positivity))
  obtain ⟨hrD, hDpos, hDm, hm, hM, hphysical⟩ :=
    henergy Λ T hT h S E₀ Ω hyp.groundState hyp.graph_eq hyp.anchor_mem (by omega)
      hyp.r₀_eq hyp.m_eq hyp.D_eq hyp.K_eq hyp.C₁_eq hyp.card_le hyp.depth_eq hyp.rows_le
      (fun x ↦ card_anchor_fiber_le S.anchor hyp.anchor_mem x) hyp.clearance htarget hsource
  obtain ⟨hK, hKL, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail,
      hwindowData⟩ := hphysical
  refine ⟨e, Ωt, htrgs, he0, he.trans (min_le_left _ _), htrace, ?_⟩
  intro E z
  obtain ⟨hwindow, hd, hpdata⟩ := hwindowData
  refine ⟨hwindow.1, hwindow.2.1, hwindow.2.2.1, hwindow.2.2.2.1, hm, hM, hd, ?_⟩
  have : NeZero E.card := NeZero.of_pos hd
  intro d β ΩX ψ Sent
  obtain ⟨ell, hpre, hmass, hdim, hweights⟩ := hpdata
  refine ⟨ell, fun k hk ↦
    ⟨(augmentedReplicaPrevector_ne_zero_iff_global q d k Ωt (ell k)).2 (hpre k hk).1,
      (norm_augmentedReplicaPrevector_eq_global q d k Ωt (ell k)).trans_le
        (hpre k hk).2⟩, ?_⟩
  intro dims energy pre σ Qpre Y gpre gpost gaps gmax W hW hasmall a round
  have ha_eq : a = W / (S.K : ℝ) := by
    simp only [a, ScannerExponents.a, ← hyp.K_eq]
  have hasmall' : (W / (S.K : ℝ)) * (S.r₀ : ℝ) ^ 2 ≤ c := by
    simpa only [ScannerExponents.a, ← hyp.K_eq] using hasmall
  obtain ⟨hroughCap, heCap, b, rem, ρD, ρE, CbAux, cRU, cR, Ci,
      hCbAux, hcRU, hcR, hCi, hb, hblog, hrem, hremLimit,
      hρD, hρDLimit, hρE, hρELimit, hRULimit, hRLimit, hselect⟩ :=
    hweights W hW hasmall'
  obtain ⟨hBnorm, hnorm⟩ := hnorm Λ T hT S hyp.graph_eq hyp.depth_eq hyp.anchor_mem
    hm hM (by omega) (X.L S.n) (by omega) hyp.r₀_eq (by omega) hDpos hDm hKL
    hyp.rows_le hyp.clearance
  have hρ : reducedState Λ q Ωt (S.target T) =
      Matrix.partialTraceRight (Matrix.vecMulVec ΩX (star ΩX)) :=
    (reducedState_eq_finiteProduct Λ q Ωt (S.target T)).trans
      (FiniteProduct.reducedPure_eq_partialTrace β Ωt (S.target T))
  have hzEq :
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian.spectralRestrictionMass E =
        z := by simp only [← hρ, z]
  have hz : 0 <
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian.spectralRestrictionMass E :=
    hzEq.symm ▸ hwindow.2.2.1
  obtain ⟨hroughLower, hsharp⟩ :=
    hnorm h Ω hΔ hyp.groundState.1 e Ωt htrgs E hd hz ell
      hpre hmass hdim W hW (hasmall'.trans hchalf)
  simp only [← ha_eq] at hroughLower hsharp hselect
  let Bmarg := Cb * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ (12 : ℕ))
  have hBnorm_le :
      CBnorm * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ (12 : ℕ)) ≤ Bmarg :=
    mul_le_mul_of_nonneg_right
      ((le_max_right CBcut CBnorm).trans (le_max_left _ _)) (by positivity)
  have hBcut_le :
      CBcut * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ (12 : ℕ)) ≤ Bmarg :=
    mul_le_mul_of_nonneg_right
      ((le_max_left CBcut CBnorm).trans (le_max_left _ _)) (by positivity)
  have hBmarg_upper :
      Bmarg ≤ Cb * (S.n : ℝ) * (X.D S.n : ℝ) * Real.log (S.n : ℝ) ^ (12 : ℝ) := by
    simpa only [Bmarg, Real.rpow_ofNat, hyp.D_eq, _root_.mul_assoc] using (le_refl Bmarg)
  obtain ⟨_, hcut⟩ :=
    hbudget Λ T hT S hyp.graph_eq hyp.depth_eq hyp.anchor_mem
      (X.L S.n) (by omega) hyp.r₀_eq (by omega)
      hDpos hDm hKL hyp.rows_le hyp.clearance
  have hstatus : ∀ (k : ℕ) (hist : History S.K S.m S.M k) (band : Fin S.K),
      (k ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band), B Q ≤ Bmarg) ∧
      (k + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band), B Q ≤ Bmarg) :=
    fun k hist band ↦
      ⟨fun hk Q hQ ↦ ((hcut k hist band).1 hk Q hQ).trans hBcut_le,
        fun hk Q hQ ↦ ((hcut k hist band).2 hk Q hQ).trans hBcut_le⟩
  let Bsh := max Ce 1 * ((S.n : ℝ) * (X.L S.n : ℝ) ^ X.e + S.n) +
    (S.n : ℝ) ^ (-247 : ℝ)
  let Bexc := 1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ)
  have hn1 : (1 : ℝ) ≤ S.n := by exact_mod_cast (show 1 ≤ S.n by omega)
  have hBsh : Bsh ≤ Cb * ((S.n : ℝ) * (X.L S.n : ℝ) ^ X.e + S.n) := calc
    Bsh ≤ max Ce 1 * ((S.n : ℝ) * (X.L S.n : ℝ) ^ X.e + S.n) +
        ((S.n : ℝ) * (X.L S.n : ℝ) ^ X.e + S.n) :=
      add_le_add_right
        ((Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num : (-247 : ℝ) ≤ 0)).trans
          (show 1 ≤ (S.n : ℝ) * (X.L S.n : ℝ) ^ X.e + S.n from
            hn1.trans (le_add_of_nonneg_left (by positivity)))) _
    _ = (max Ce 1 + 1) * ((S.n : ℝ) * (X.L S.n : ℝ) ^ X.e + S.n) := by ring
    _ ≤ Cb * ((S.n : ℝ) * (X.L S.n : ℝ) ^ X.e + S.n) :=
      mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
  have hBexc : Bexc ≤ Cb * (S.n : ℝ) * (X.D S.n : ℝ) := calc
    Bexc = 1 + (3 * Real.log q) * ((S.n : ℝ) * S.D) := by dsimp only [Bexc]; ring
    _ ≤ (S.n : ℝ) * S.D + (3 * Real.log q) * ((S.n : ℝ) * S.D) :=
      add_le_add_left
        (one_le_mul_of_one_le_of_one_le hn1 (by exact_mod_cast hDpos)) _
    _ = (1 + 3 * Real.log q) * ((S.n : ℝ) * S.D) := by ring
    _ ≤ Cb * ((S.n : ℝ) * S.D) :=
      mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
    _ = Cb * (S.n : ℝ) * (X.D S.n : ℝ) := by rw [hyp.D_eq, _root_.mul_assoc]
  have ha : 0 < a := ha_eq.symm ▸
    div_pos (zero_lt_one.trans_le hW) (Nat.cast_pos.mpr (by omega))
  have hWa : a * (S.K : ℝ) = W := by
    rw [ha_eq, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (show S.K ≠ 0 by omega))]
  have htr := Matrix.isGappedGroundState_iff.mp htrgs
  have hsh : ∀ j : Fin (X.L S.n + 1),
      FiniteProduct.entropy β Ωt
        (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤ Bsh := fun j ↦ by
    simpa only [regionalEntropy_eq_finiteProduct] using
      hprefix S.n ((le_max_right N Ne).trans hn) Λ Ω Ωt hyp.groundState.1 htr.1
        S.A S.depth (X.L S.n) hcard htrace
        (max Ce 1) X.e hsource j.val (Nat.le_of_lt_succ j.isLt)
  obtain ⟨cEnd, hcEnd, hlimEnd, hupperEnd⟩ :=
    eventually_actualScan_suppliedPrevector_rough_upper hT S
      hyp.graph_eq hyp.depth_eq hm hM a ha
      (show 0 < S.n by omega) (show S.r₀ ≤ S.D by omega)
      hDpos hDm (X.L S.n) hKL hyp.rows_le Ωt htr.1 E ell Bsh hsh hz hmass
  simp only [hWa] at hupperEnd
  let Bnorm : ℝ := CBnorm * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
  classical
  have hsharpChoice :
      ∃ cSU cSL CfSL : ℝ, 0 ≤ cSU ∧ 0 ≤ cSL ∧ 0 ≤ CfSL ∧
        Tendsto (Real.bellOverlapRemainder d cSU S.K) atTop (𝓝 0) ∧
        Tendsto (sharpLowerRemainder a cSL CfSL ell Sent) atTop (𝓝 0) ∧
        ∀ᶠ k : ℕ in atTop, ∀ (s : Fin (S.n * S.m)) (p : ℝ),
          a * Real.sqrt Bnorm ≤ min c₀ 1 / 10 →
          let D := S.actualChargeData hm hM s.val
          let tree := (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
            (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
          let Nsq := Matrix.Transport.filteredNormSq
            (D.rootPath dims (a / 2) k p) (pre k)
          let defect :=
            ((S.actualChargeScanRound hm hM s.val dims energy a pre).meanEnergy k p - e) /
              (g / 2)
          0 < Nsq ∧
            -Real.log Nsq / (k : ℝ) ≤
              2 * Real.log (d : ℝ) - Real.log z +
                (a / 2) * (∑ band, ∑ j, tree.weight j * gpost j band) +
                  6 * (S.K : ℝ) * (C₀ * Bnorm) * a ^ 2 -
                    (S.K : ℝ) / 2 * Real.log z +
                      Real.bellOverlapRemainder d cSU S.K k ∧
            ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
              let sharpRate := fun band ↦ 2 * Sent +
                (1 - τ) * (∑ j, tree.weight j * gpre j band) -
                  τ * (2 * Real.log (d : ℝ)) - (3 + 1 / a) * Real.binEntropy τ -
                    25 * (C₀ * Bnorm) * a
              (a / 2) * (∑ band,
                (sharpRate band - defect / τ * max 0 (2 * Sent + gmax) -
                  sharpLowerRemainder a cSL CfSL ell Sent k)) ≤
                    -Real.log Nsq / (k : ℝ) := by
    by_cases hsmall : a * Real.sqrt Bnorm ≤ min c₀ 1 / 10
    case neg =>
      exact ⟨0, 0, 0, le_rfl, le_rfl, le_rfl,
        Real.tendsto_bellOverlapRemainder d 0 S.K,
        tendsto_sharpLowerRemainder_of_label_dimension ell Sent hdim a 0 0,
        Filter.Eventually.of_forall fun _ _ _ hs ↦ (hsmall hs).elim⟩
    obtain ⟨cSU, cSL, CfSL, hcSU, hcSL, hCfSL, hSULimit, hSLLimit, hSharpAll⟩ :=
      hsharp hsmall
    refine ⟨cSU, cSL, CfSL, hcSU, hcSL, hCfSL, hSULimit, hSLLimit, ?_⟩
    filter_upwards [hSharpAll] with k hk
    intro s p _
    refine ⟨(hk s p).1, ?_, (hk s p).2.2⟩
    rw [← hzEq]
    exact (hk s p).2.1
  obtain ⟨cSU, cSL, CfSL, hcSU, hcSL, hCfSL, hSULimit, hSLLimit, hSharpAll⟩ := hsharpChoice
  obtain ⟨cRL, CfRL, hcRL, hCfRL, hRLLimit, hRLall⟩ := hroughLower
  have hρSumLimit : Tendsto (fun k ↦ ρD k + ρE k) atTop (𝓝 0) := by
    simpa only [add_zero] using hρDLimit.add hρELimit
  have hC0 : 0 ≤ C₀ :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le)
      (div_nonneg (by norm_num) hg.le)
  have hBudgetErrors :
      (6 * (S.K : ℝ) * (C₀ * Bnorm) * a ^ 2 ≤
        6 * (S.K : ℝ) * (C₀ * Bmarg) * a ^ 2) ∧
      (25 * (C₀ * Bnorm) * a ≤ 25 * (C₀ * Bmarg) * a) :=
    ⟨mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hBnorm_le hC0) (by positivity)) (sq_nonneg a),
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hBnorm_le hC0) (by norm_num)) ha.le⟩
  have hendpoint : ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ r : Fin (X.rounds S.n),
        r.val + 1 = X.rounds S.n →
          -(round r).logNormSq k 1 / (k : ℝ) ≤
            2 * Real.log d - Real.log z +
              2 * (1 / 4) * W * (2 * Bsh / z + 2 * Bexc) + ρ k := by
    refine ⟨Real.bellOverlapRemainder d cEnd S.K, hlimEnd, ?_⟩
    filter_upwards [hupperEnd] with k hk
    intro r hlast
    have hlast' : r.val + 1 = 2 * (S.n * S.m) := by
      simpa only [ScannerExponents.rounds, ← hyp.m_eq, Nat.mul_assoc] using hlast
    have hcharge : IsChargeRound r.val := by
      change r.val % 2 = 1
      omega
    have hstage : r.val / 2 + 1 ≤ S.n * S.m := by omega
    have hc := (hk (r.val / 2) hstage (1 : ℝ)).2.2
    change -(S.actualScanRound hm hM dims energy a pre r.val).logNormSq k 1 /
      (k : ℝ) ≤ _
    rw [S.actualScanRound_of_charge hm hM dims energy a pre hcharge]
    change -Real.log (Matrix.Transport.filteredNormSq
      ((S.actualChargeData hm hM (r.val / 2)).rootPath dims (a / 2) k 1) (pre k)) /
      (k : ℝ) ≤ _
    calc
      _ ≤ 2 * Real.log d - Real.log z + W * (Bsh / z + Bexc) +
          Real.bellOverlapRemainder d cEnd S.K k := by
        rw [← hzEq]
        exact hc
      _ = 2 * Real.log d - Real.log z +
          2 * (1 / 4) * W * (2 * Bsh / z + 2 * Bexc) +
          Real.bellOverlapRemainder d cEnd S.K k := by ring
  refine ⟨Bsh, Bexc, Bmarg, hBsh, hBexc, hBnorm.trans hBnorm_le, hBmarg_upper,
    (fun Y u hu ↦ S.log_surprisalMoment_truncated_reducedState_le h Ω
      hyp.graph_eq hyp.anchor_mem hΔ hyp.groundState.1 (X.L S.n) htrgs Y hu),
    hstatus, hendpoint, (fun k ↦ ρD k + ρE k), cRU, cRL, CfRL, cSU, cSL, CfSL,
    hρSumLimit, hcRU, hcRL, hCfRL, hcSU, hcSL, hCfSL,
    hRULimit, hRLLimit, hSULimit, hSLLimit, ?_⟩
  filter_upwards [hselect, hSharpAll, eventually_gt_atTop (0 : ℕ)] with k hkSelect hkSharp hkpos
  obtain ⟨s, p, hp, hDensity, _, _, hEnergy, hNsq, hRU⟩ := hkSelect
  let r : Fin (X.rounds S.n) := ⟨2 * s.val + 1, by
    simp only [ScannerExponents.rounds, ← hyp.m_eq, Nat.mul_assoc]
    omega⟩
  have hrCharge : IsChargeRound r.val := by
    change (2 * s.val + 1) % 2 = 1
    omega
  have hround : round r = S.actualChargeScanRound hm hM s.val dims energy a pre := by
    simpa only [show r.val / 2 = s.val by dsimp only [r]; omega] using
      S.actualScanRound_of_charge hm hM dims energy a pre hrCharge
  refine ⟨r, by simpa only [ScannerExponents.chargeRounds, Finset.mem_filter,
    Finset.mem_univ, true_and] using hrCharge, s, rfl, p, hp, ?_⟩
  rw [hround]
  refine ⟨?_, ?_, hNsq, (hRLall k hkpos s p).2.2.1, hRU,
    (hRLall k hkpos s p).2.2.2, ?_⟩
  case refine_1 =>
    rw [S.actualChargeScanRound_chargeDefect hm hM s.val dims energy a pre ha.le k p,
      ← hyp.K_eq, ← hyp.D_eq]
    exact hDensity.trans (_root_.add_le_add le_rfl
      (le_add_of_nonneg_right (hρE k)))
  case refine_2 =>
    rw [← hyp.D_eq]
    convert hEnergy.trans (_root_.add_le_add le_rfl
      (le_add_of_nonneg_left (hρD k))) using 1
    · rfl
    · ring
  intro hsmallMarg
  obtain ⟨_, hSU, hSL⟩ := hkSharp s p
    ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBnorm_le) ha.le).trans hsmallMarg)
  refine ⟨hSU.trans (_root_.add_le_add
    (sub_le_sub (_root_.add_le_add le_rfl hBudgetErrors.1) le_rfl) le_rfl), ?_⟩
  intro τ hτ hτhalf
  refine le_trans ?_ (hSL τ hτ hτhalf)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_)
    (div_nonneg ha.le (by norm_num))
  intro band _
  exact sub_le_sub
    (sub_le_sub (sub_le_sub le_rfl hBudgetErrors.2) le_rfl) le_rfl

end CollarScan

end TNLean.PEPS.AreaLaw.Scan
