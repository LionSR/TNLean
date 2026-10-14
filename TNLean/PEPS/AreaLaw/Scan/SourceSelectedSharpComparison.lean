/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceTargetSharpMoments
import TNLean.PEPS.AreaLaw.Scan.ActualSelectedSharpComparison
import TNLean.PEPS.AreaLaw.Scan.SourceEndpointRoughBudget
import TNLean.PEPS.AreaLaw.Scan.RoughSelectionBudget
import TNLean.PEPS.AreaLaw.GlobalSchmidtBellPrevector

/-!
# One physical target witness and its selected actual sharp comparison

The target-window theorem is invoked once. Its same truncated ground vector
supplies the sharp moments and chooses one physical Schmidt--Bell sequence
before the total weight. The actual selector, uniform transport energy,
fixed-scale coefficient theorem and both sharp rates are then instantiated.
No selected-point, coefficient-cap or norm-comparison conclusion is a premise.

The original-state prefix entropy input supplies the actual rough endpoint
budget and an explicit selected-density bound. Transport smallness and geometric
separation remain explicit. This does not prove the final density power, safe-box entropy
bounds or Proposition 9.6. See
`docs/paper-gaps/arealaw2d_source_selected_sharp_comparison_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 130--153, 240--281 and 383--418;
`08-scanner.tex`, lines 400--533 and 839--911, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter ActualTerminals

private def sourceSharpExponents : ScannerExponents :=
  { ell := (Exponents.scannerEll : ℝ)
    kappa := (Exponents.scannerKappa : ℝ)
    mu := (Exponents.scannerMu : ℝ)
    nu := (Exponents.scannerNu : ℝ)
    e := (Exponents.boxError : ℝ)
    ell_pos := by norm_num [Exponents.scannerEll]
    ell_lt_one := by norm_num [Exponents.scannerEll]
    kappa_pos := by norm_num [Exponents.scannerKappa]
    kappa_lt_mu := by norm_num [Exponents.scannerKappa, Exponents.scannerMu]
    mu_lt_one_sub_ell := by norm_num [Exponents.scannerMu, Exponents.scannerEll]
    nu_pos := by norm_num [Exponents.scannerNu]
    e_pos := by norm_num [Exponents.boxError]
    e_lt_one := by norm_num [Exponents.boxError]
    kappa_le_e := by norm_num [Exponents.scannerKappa, Exponents.boxError] }

private theorem augmented_prevector_properties_of_global
    {V : Type} [Fintype V] [DecidableEq V] (q d k : ℕ)
    (Ω : (V → Fin q) → ℂ) (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (H : Matrix (V → Fin q) (V → Fin q) ℂ) (e : ℝ)
    (hne : WithLp.toLp 2 (replicaPrevector Ω d k ell ∘
      globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k) ≠ 0)
    (heigen : Matrix.globalReplicaMeanHamiltonian (fun _ : V ↦ Fin q) (Fin d) (Fin d) H k *ᵥ
        (replicaPrevector Ω d k ell ∘
          globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k) =
      (e : ℂ) • (replicaPrevector Ω d k ell ∘
        globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k)) :
    let dims := augmentedDimensions (V := V) q (fun _ ↦ d)
    let pre := replicaPrevector Ω d k ell ∘ augmentedSumReplicaCopiesEquiv q d k
    pre ≠ 0 ∧ pre ∈ symmetricSubspace k (fun v ↦ Fin (dims v)) ∧
      copyMean dims k (augmentOperator q (fun _ ↦ d) H) *ᵥ pre = (e : ℂ) • pre := by
  classical
  intro dims pre
  let ecoord := augmentedReplicaConfigurationEquiv (V := V) q d k
  have hpreEq : pre ∘ ecoord = replicaPrevector Ω d k ell ∘
      globalReplicaCopiesEquiv (fun _ : V ↦ Fin q) (Fin d) (Fin d) k := by
    simp only [pre, augmentedSumReplicaCopiesEquiv, Equiv.coe_trans,
      Function.comp_assoc, ecoord, Equiv.symm_comp_self, Function.comp_id]
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    apply hne
    rw [← hpreEq, hz]
    rfl
  · have hfixed : symProj (copyPerm ((v : V ⊕ Bool) → Fin (dims v)) k) *ᵥ pre = pre :=
      symProj_mulVec_augmentedReplicaPrevector q d k Ω ell
    rw [← hfixed]
    exact symProj_mulVec_mem _ _
  · have hglobal : Matrix.globalReplicaMeanHamiltonian (fun _ : V ↦ Fin q)
        (Fin d) (Fin d) H k *ᵥ (pre ∘ ecoord) = (e : ℂ) • (pre ∘ ecoord) := by
      rw [hpreEq]
      exact heigen
    rw [copyMean_augmentOperator_eq_globalReplicaMeanHamiltonian]
    ext x
    simpa only [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
      Function.comp_apply, ecoord, Equiv.apply_symm_apply, Pi.smul_apply] using
      congrFun hglobal (ecoord.symm x)

private theorem selected_density_of_rough_endpoint
    {k n m D K d : ℕ} {a W C₁ width Q endpoint Brough rate b : ℝ}
    (hk : 0 < k) (hn : 0 < n) (hm : 0 < m) (hD : 0 < D) (hK : 0 < K)
    (ha : 0 < a) (hC : 0 < C₁) (hwidth : 0 < width) (hW : a * (K : ℝ) = W)
    (c Ci Cb : ℝ)
    (hendpoint : endpoint / (k : ℝ) ≤ Brough + roughEndpointRemainder d c K Ci k)
    (hb : b ≤ Cb * Real.log ((k : ℝ) + 2))
    (hselection : Q ≤ (endpoint + (2 * n * m : ℕ) * ((k : ℝ) * rate + b)) /
      (((k : ℝ) * a * ((1 / (2 * (C₁ + 1))) / ((n : ℝ) * D))) *
        ((n * m : ℕ) : ℝ) * width)) :
    Q / (K * n * D : ℝ) ≤ (2 * (C₁ + 1) / (W * ((n * m : ℕ) : ℝ) * width)) *
      (Brough + (2 * n * m : ℕ) * rate +
        roughEndpointRemainder d c K (Ci + (2 * n * m : ℕ) * Cb) k) := by
  have hbudget := roughSelectionBudget_le_of_endpoint_budget (H := n * m)
    hk c Ci Cb endpoint Brough rate b hendpoint hb
  have hdensity := selected_density_le_of_normalized_budget hk hn hm hD hK ha hC hwidth
    hbudget (by simpa only [Nat.mul_assoc] using hselection)
  simpa only [hW, Nat.mul_assoc] using hdensity

open Classical in
/-- A single truncated target window and a single physical label sequence
produce an actual selected charge comparison at the literal final scales.
The source, transport and coefficient constants and the size threshold
precede the physical system; the state, spectral set and labels precede the
total weight. Replica-remainder constants are chosen after the fixed physical
data and weight, before the interval, replica count and selected point.
Both sharp remainders are uniform in that selected point.

The original-state prefix entropy input is transferred to this same state
and bounds the actual endpoint logarithms. The selector's density bound
retains its vanishing remainder. Transport smallness and geometric inequalities
remain explicit. Source: `08-scanner.tex`, lines 400--533 and 839--911. -/
theorem exists_sourceTarget_selected_actualCharge_sharp_comparison
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ) :
    ∃ Ctr Ctarget CB ct Cent eent Cen een C Cl : ℝ,
      0 < Ctr ∧ 0 < Ctarget ∧ 0 < CB ∧ 0 < ct ∧ 1 ≤ C ∧ 0 ≤ Cl ∧
      ∃ N : ℕ, 2 ≤ N ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
          (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
          (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) → N ≤ S.n →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          S.m = ⌊(S.n : ℝ) ^ (Exponents.scannerMu : ℝ)⌋₊ →
          S.D = ⌈(S.n : ℝ) ^ (Exponents.scannerKappa : ℝ)⌉₊ →
          S.K = ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ / (8 * S.m) →
          S.C₁ = C₁ → (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ r : ℕ, 1 ≤ r →
            r ≤ ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ →
            (ambientDilation T r \ ambientDilation T (r - 1)).card ≤ S.n) →
          (∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ multiplicity) →
          (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
            ((2 * ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ +
              10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
          ∀ Ce η : ℝ,
          (∀ j : ℕ, j ≤ ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ →
            regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
              Ce * ((S.n : ℝ) *
                ((⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ : ℕ) : ℝ) ^ η + S.n)) →
          2 * S.r₀ ≤ S.D → ∀ (hDpos : 1 ≤ S.D) (hDm : 4 * S.D ≤ S.m),
          ∃ (hm : 0 < S.m) (hM : 0 < S.M),
          let L := ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
          let δtail := (S.n : ℝ) ^ (-100 : ℝ)
          let B := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
          let C₀ := 512 * Real.exp 1 * (2 / g)
          let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ η + S.n) +
            (S.n : ℝ) ^ (-247 : ℝ)
          1 ≤ S.K ∧ 8 * S.K * S.m ≤ L ∧ 1 ≤ B ∧
          ((S.truncationSet L).card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 ∧
          X ⊆ S.truncationSet L ∧
          ∃ (e : ℝ) (Ωt : StateSpace Λ q),
            IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt (g / 2) ∧
            0 ≤ e ∧ e ≤ ε ∧
            Matrix.traceDistance
                (Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))
                (Matrix.vecMulVec Ω.ofLp (star Ω.ofLp)) ≤ Real.sqrt (2 * ε / g) ∧
            cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X ≤
              Ctarget * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
            Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
              (regionalEntropy Λ q Ωt X) w ≤ δtail ∧
            let E := Entropy.typicalSet (reducedState_isHermitian Λ q Ωt X).eigenvalues
              (regionalEntropy Λ q Ωt X) w
            let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
            (0 < 1 - δtail ∧ 1 - δtail ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
              ∀ i ∈ E, 0 < (reducedState_isHermitian Λ q Ωt X).eigenvalues i ∧
                Real.exp (-regionalEntropy Λ q Ωt X - w) ≤
                  (reducedState_isHermitian Λ q Ωt X).eigenvalues i ∧
                (reducedState_isHermitian Λ q Ωt X).eigenvalues i ≤
                  Real.exp (-regionalEntropy Λ q Ωt X + w)) ∧
            ∃ hd : 0 < E.card,
            letI : NeZero E.card := ⟨Nat.ne_of_gt hd⟩
            let d := E.card
            let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
              (FiniteProduct.splitEquiv β X) Ωt
            let ψ : FiniteProduct.Configuration β Xᶜ × Fin d → ℂ := fun x ↦
              compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
            let Sent := vonNeumannEntropy (Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)))
              (Matrix.posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian
            let dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
            let energy := S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)
            let σ := terminalPartition S (S.n * S.m)
            let near := fun j band ↦ receiving (σ j band) false
            let middleRegion := fun j band ↦ middle (σ j band)
            let gpre := fun j band ↦ FiniteProduct.entropy β Ωt (near j band) +
              FiniteProduct.entropy β Ωt (near j band ∪ middleRegion j band)ᶜ -
              FiniteProduct.entropy β Ωt (middleRegion j band)
            let gpost := fun j band ↦
              regionalEntropy Λ q Ωt (positiveNear S.depth (σ j band)) +
                regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j band)) -
                regionalEntropy Λ q Ωt (middle (σ j band))
            let gaps := (Finset.univ :
              Finset (terminalFamily S.K S.m S.M (S.n * S.m) × Fin S.K)).image
                (fun j ↦ gpre j.1 j.2)
            let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
            let tree := fun (s : Fin (S.n * S.m)) (p : ℝ) ↦
              ((S.actualChargeData hm hM s.val).tree
                (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
                (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
            let Gpre := fun s p ↦
              (∑ band, ∑ j, (tree s p).weight j * gpre j band) / (S.K : ℝ)
            let Gpost := fun s p ↦
              (∑ band, ∑ j, (tree s p).weight j * gpost j band) / (S.K : ℝ)
            ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
              let pre : (k : ℕ) → Config k (fun v ↦ Fin (dims v)) → ℂ := fun k ↦
                replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
              (∀ k : ℕ, 0 < k →
                let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
                  globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
                ξ ≠ 0 ∧ ‖ξ‖ ≤ 1) ∧
              Asymptotics.IsLittleO atTop
                (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) * Sent)
                (fun k : ℕ ↦ (k : ℝ)) ∧
              ∀ W : ℝ, 0 < W → W ≤ (S.n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
                let a := W / (S.K : ℝ)
                let ℓ := transportLogDimBound q S.r₀
                a * ℓ ≤ ct →
                let Brough := 2 * Real.log (d : ℝ) - Real.log z + W *
                  (Bsh / z + (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log (q : ℝ)))
                let rate := Cent * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent
                ∃ (b rem : ℕ → ℝ) (Cb cU cL Cf cR Ci : ℝ),
                  0 ≤ Cb ∧ 0 ≤ cU ∧ 0 ≤ cL ∧ 0 ≤ Cf ∧ 0 ≤ cR ∧ 0 ≤ Ci ∧
                  (∀ k, 0 ≤ b k) ∧ (∀ k, b k ≤ Cb * Real.log (k + 2)) ∧
                  (∀ k, 0 ≤ rem k) ∧ Tendsto rem atTop (𝓝 0) ∧
                  Tendsto (Real.bellOverlapRemainder d cU S.K) atTop (𝓝 0) ∧
                  Tendsto (sharpLowerRemainder a cL Cf ell Sent) atTop (𝓝 0) ∧
                  Tendsto (roughEndpointRemainder d cR S.K
                    (Ci + (2 * S.n * S.m : ℕ) * Cb)) atTop (𝓝 0) ∧
                  ∀ p₀ p₁ : ℝ, 0 < p₀ → p₀ < p₁ → p₁ < 1 →
                    ∀ᶠ k : ℕ in atTop,
                      ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc p₀ p₁,
                        let Q := S.actualChargeEntropyDefect hm hM s.val dims energy
                          (a / 2) k (pre k) p
                        let defect :=
                          ((S.actualChargeScanRound hm hM s.val dims energy a pre).meanEnergy k p -
                            e) /
                            (g / 2)
                        let cap := C * W ^ 2 * (S.n : ℝ) ^ (Exponents.scannerEll : ℝ) *
                          (S.D : ℝ) ^ 2 * (Real.log S.n) ^ Cl *
                            ((1 - p) * (Q / (S.K * S.n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                              (1 - p) * (S.n : ℝ) ^ (-P) + p)
                        Q / (S.K * S.n * S.D : ℝ) ≤
                          (2 * (S.C₁ + 1) / (W * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀))) *
                            (Brough + (2 * S.n * S.m : ℕ) * rate +
                              roughEndpointRemainder d cR S.K
                                (Ci + (2 * S.n * S.m : ℕ) * Cb) k) ∧
                        0 ≤ defect ∧ defect ≤ (e + cap + rem k) / (g / 2) ∧
                        ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                          2 * Sent + Gpre s p - Gpost s p ≤
                            2 * (2 * Real.log (d : ℝ) - Real.log z) / W +
                              τ * Gpre s p + 2 * τ * Real.log (d : ℝ) +
                              (3 + 1 / a) * Real.binEntropy τ + 37 * (C₀ * B) * a -
                              Real.log z / a + ((e + cap + rem k) / (g / 2)) / τ *
                                max 0 (2 * Sent + gmax) +
                              2 * Real.bellOverlapRemainder d cU S.K k / W +
                                sharpLowerRemainder a cL Cf ell Sent k := by
  classical
  obtain ⟨ct, Cent, eent, Cen, een, hct, hselector⟩ :=
    actualCharges_selection_energy_domainGraph
  obtain ⟨Ctr, Ctarget, CB, hCtr, hCtarget, hCB, htarget⟩ :=
    exists_truncated_target_sharp_moments hq R hJ hΔ hC_T
  have hmargin : (Exponents.scannerOmega : ℝ) + (1 + sourceSharpExponents.kappa) / 2 <
      1 - sourceSharpExponents.ell - sourceSharpExponents.mu := by
    norm_num [sourceSharpExponents, Exponents.scannerOmega, Exponents.scannerKappa,
      Exponents.scannerEll, Exponents.scannerMu]
  obtain ⟨Nt, hNt, ht⟩ := htarget sourceSharpExponents
    (Exponents.scannerOmega : ℝ) hmargin
  obtain ⟨C, Cl, hC, hCl, Nc, hc⟩ :=
    exists_actualCharge_energy_coefficients q hCtr hC₁ hC_T multiplicity P Cen een
  obtain ⟨Ne, hNe, hendpoint⟩ :=
    exists_source_actualScan_suppliedPrevector_endpoint_budget hq
      (Δ / positiveNormalization 1 (Δ / 2) J) (C_T + 1)
      (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))
  refine ⟨Ctr, Ctarget, CB, ct, Cent, eent, Cen, een, C, Cl,
    hCtr, hCtarget, hCB, hct, hC, hCl, max Nt (max Nc Ne),
    hNt.trans (le_max_left _ _), ?_⟩
  intro Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear Ce η hsource hrD hDpos hDm
  have hnT : Nt ≤ S.n := (le_max_left _ _).trans hn
  have hnC : Nc ≤ S.n := (le_max_left Nc Ne).trans ((le_max_right _ _).trans hn)
  have hnE : Ne ≤ S.n := (le_max_right Nc Ne).trans ((le_max_right _ _).trans hn)
  have hn2 : 2 ≤ S.n := hNt.trans hnT
  have hCp : 0 < S.C₁ := hCeq.symm ▸ hC₁
  have hCm : 3 * (multiplicity : ℝ) ≤ S.C₁ := hCeq.symm ▸ hmultiplicity
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hCp (le_trans (by decide) hn2) hDpos
  refine ⟨hm, hM, ?_⟩
  intro L X β g ε w δtail B C₀ Bsh
  obtain ⟨hK, _, hKL, hB, hC₀, hc₀, hcard, hX, _, e, Ωt, htrgs, he0, he,
      _, htrace, _, _, hBX, htail, hwindow, hmom, hsmall⟩ :=
    ht Λ T hT h S E₀ Ω hgs hgraph hanchor hnT hr hmScale hDScale hKScale
      hsize hdepth hrows hclear
  obtain ⟨_, _, hcoefficient⟩ := hc S.n hnC Λ T hT R S rfl hmScale hKScale
    hDScale hr hCeq hsize hgraph hdepth hclear hrows hmult
  refine ⟨hK, hKL, hB, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, ?_⟩
  intro E z
  have hd : 0 < E.card := Finset.card_pos.mpr hwindow.2.2.2.2.1
  refine ⟨hwindow, hd, ?_⟩
  intro inst
  letI : NeZero E.card := inst
  intro d ΩX ψ Sent dims energy σ near middleRegion gpre gpost gaps gmax tree Gpre Gpost
  have hρ : reducedState Λ q Ωt X =
      Matrix.partialTraceRight (Matrix.vecMulVec ΩX (star ΩX)) :=
    (reducedState_eq_finiteProduct Λ q Ωt X).trans
      (FiniteProduct.reducedPure_eq_partialTrace β Ωt X)
  have hzEq :
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian.spectralRestrictionMass E =
        z := by simp only [← hρ]
  have hz : 0 <
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian.spectralRestrictionMass E :=
    hzEq.symm ▸ hwindow.2.2.1
  have htr := Matrix.isGappedGroundState_iff.mp htrgs
  obtain ⟨ell, hphysical, hmass, hdim⟩ :=
    exists_global_schmidtBellPrevector (∑ i, S.truncatedEnergyTerm h Ω Δ L i)
      Ωt e htr.1 htr.2.1 X E hz
  refine ⟨ell, ?_⟩
  intro pre
  have hpre : ∀ k : ℕ, 0 < k →
      let ξ := WithLp.toLp 2 (replicaPrevector Ωt d k (ell k) ∘
        globalReplicaCopiesEquiv β (Fin d) (Fin d) k)
      ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := fun k hk ↦ ⟨(hphysical k hk).1, (hphysical k hk).2.1⟩
  refine ⟨hpre, hdim, ?_⟩
  intro W hW hWle a ℓ hasmall Brough rate
  obtain ⟨ha, har, haone, _, _⟩ := hsmall W hW hWle
  have hKr : (0 : ℝ) < S.K := by exact_mod_cast (show 0 < S.K by omega)
  have hWa : a * (S.K : ℝ) = W := div_mul_cancel₀ W hKr.ne'
  have hg : 0 < g := div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  obtain ⟨b, rem, Cb, hCb, hb0, hb, hrem0, hrem, hselect⟩ :=
    hselector (d := d) h Ω S hT hgraph hdepth hanchor hΔ hgs.1 hn2 hrD hDpos hDm
      hKL hCp hCm hrows hmult hclear ha hasmall
  obtain ⟨cU, cL, Cf, hcU, hcL, hCf, hlimU, hlimL, hsharp⟩ :=
    eventually_actualCharge_suppliedPrevector_sharp_comparison hT S hdepth hm hM
      (show 0 < S.K by omega) h Ω Δ L hKL Ωt e (g / 2) htr.1 htr.2.2
      (half_pos hg) a (C₀ * B) _ ha har haone
      (mul_nonneg hC₀.le (zero_le_one.trans hB)) E ell
      hmom hz hpre hmass hdim
  simp only [hzEq, hWa] at hsharp
  obtain ⟨cR, Ci, hcR, hCi, _, hend⟩ :=
    hendpoint hT S hnE hgraph hdepth hm hM a ha (show S.r₀ ≤ S.D by omega)
      hDpos hDm L hKL hrows Ω Ωt hgs.1 htr.1 hcard htrace Ce η hsource
      E ell hz (fun k hk ↦ (hpre k hk).2) hmass
  simp only [hzEq, hWa] at hend
  refine ⟨b, rem, Cb, cU, cL, Cf, cR, Ci, hCb, hcU, hcL, hCf, hcR, hCi,
    hb0, hb, hrem0, hrem, hlimU, hlimL,
    tendsto_roughEndpointRemainder d cR S.K (Ci + (2 * S.n * S.m : ℕ) * Cb), ?_⟩
  intro p₀ p₁ hp₀ hp₀₁ hp₁
  filter_upwards [hsharp, hend, eventually_gt_atTop 0] with k hsharpK hendK hk
  obtain ⟨hnonzero, hsym, heigen⟩ := augmented_prevector_properties_of_global
    q d k Ωt (ell k) (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e
      (hphysical k hk).1 (hphysical k hk).2.2.1
  obtain ⟨s, p, hp, hQ, henergy⟩ :=
    hselect pre k hk hsym hnonzero e heigen p₀ p₁ hp₀ hp₀₁ hp₁
  have hrate : Cent * (k : ℝ) * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent =
      (k : ℝ) * rate := by dsimp only [rate]; ring
  have hdensity := selected_density_of_rough_endpoint hk
    (show 0 < S.n by omega) hm (show 0 < S.D by omega) (show 0 < S.K by omega)
    ha hCp (sub_pos.mpr hp₀₁) hWa cR Ci Cb hendK.2 (hb k) (by
      simpa only [hrate] using hQ)
  have hpInterior : p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hp₀.trans_le hp.1, hp.2.trans_lt hp₁⟩
  have hcoeff := hcoefficient (fun _ ↦ d) J h Ω Δ s.val
    (Nat.succ_le_of_lt s.isLt) W hW.le k pre hsym hnonzero p hpInterior
  have hcap := S.actualCharge_defect_le_of_density_energy_bound hm hM s.val h Ω L
    hΔ W Cen een C Cl P (rem k) e hW.le pre k p henergy hcoeff
  refine ⟨s, p, hp, hdensity, (hsharpK s p).2.1, hcap, ?_⟩
  intro τ hτ hτhalf
  have hmassLoss := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hcap hτ.le) (le_max_left (0 : ℝ) (2 * Sent + gmax))
  have hcomparison := (hsharpK s p).2.2 τ hτ hτhalf
  linarith only [hcomparison, hmassLoss]

end TNLean.PEPS.AreaLaw.Scan.CollarScan
