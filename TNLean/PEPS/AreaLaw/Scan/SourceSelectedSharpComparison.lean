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
bounds or Proposition 9.6.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 130--153, 240--281 and 383--418;
`08-scanner.tex`, lines 400--533 and 839--911, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter ActualTerminals

/-- The explicit threshold of the selected actual sharp comparison: the sharp marginal-moment
threshold at the final exponents and `ω = 1/20000`, the final actual charge-energy threshold, and
the endpoint-budget threshold `max (truncationEntropyThreshold q g (C_T + 1)) 2`
(`08-scanner.tex`, lines 400--533 and 839--911). -/
noncomputable def sourceSelectedSharpThreshold (q R : ℕ) (Ctr g C₁ C_T : ℝ) (multiplicity : ℕ)
    (P : ℝ) : ℕ :=
  max (targetSharpMomentThreshold q R Ctr g finalSharpScannerExponents
      (Exponents.scannerOmega : ℝ))
    (max (finalActualChargeEnergyThreshold Ctr C₁ C_T multiplicity P)
      (max (truncationEntropyThreshold q g (C_T + 1)) 2))

open Classical in
/-- The selected actual sharp comparison of
`exists_sourceTarget_selected_actualCharge_sharp_comparison_of_finiteFamilyTransportBound` at
the named truncation constant `Ctr = latticeTruncationRadiusConstant R J Δ (C_T + 1)`, which
depends only on `R, J, Δ, C_T`, and at any transport constants satisfying the finite-family
transport bound. Source: `08-scanner.tex`, lines 400--533 and 839--911. -/
theorem sourceTarget_selected_actualCharge_sharp_comparison_explicit
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ)
    {ct Cent eent Cen een : ℝ} (htransport : FiniteFamilyTransportBound ct Cent eent Cen een)
    {Ctr : ℝ} (hCtrEq : Ctr = latticeTruncationRadiusConstant R J Δ (C_T + 1)) :
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
          (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
          (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
          sourceSelectedSharpThreshold q R Ctr (Δ / positiveNormalization 1 (Δ / 2) J) C₁ C_T
            multiplicity P ≤ S.n →
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
          2 * S.r₀ ≤ S.D → ∀ (_hDpos : 1 ≤ S.D) (_hDm : 4 * S.D ≤ S.m),
          ∃ (hm : 0 < S.m) (hM : 0 < S.M),
          let L := ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
          let δtail := (S.n : ℝ) ^ (-100 : ℝ)
          let B := statusMarginalBudgetConstant q R Ctr *
            ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
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
              targetBudgetConstant q R Ctr * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
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
                        let cap := actualChargeEnergyCoefficient q Ctr multiplicity Cen een *
                          W ^ 2 * (S.n : ℝ) ^ (Exponents.scannerEll : ℝ) * (S.D : ℝ) ^ 2 *
                          (Real.log S.n) ^ transportLogExponent een (een + 1 / 8) *
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
  have htarget := truncated_target_sharp_moments_explicit hq R hJ hΔ hC_T hCtrEq
  have hCtr : 0 < Ctr := by
    rw [hCtrEq]; exact latticeTruncationRadiusConstant_pos R hΔ (by positivity)
  have hmargin : (Exponents.scannerOmega : ℝ) + (1 + finalSharpScannerExponents.kappa) / 2 <
      1 - finalSharpScannerExponents.ell - finalSharpScannerExponents.mu := by
    norm_num [finalSharpScannerExponents, Exponents.scannerOmega, Exponents.scannerKappa,
      Exponents.scannerEll, Exponents.scannerMu]
  have ht := htarget finalSharpScannerExponents (Exponents.scannerOmega : ℝ) hmargin
  intro Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear Ce η hsource hrD hDpos hDm
  simp only [sourceSelectedSharpThreshold, max_le_iff] at hn
  obtain ⟨hnT, hnC, hnE, hn2⟩ := hn
  have hnE : max (truncationEntropyThreshold q (Δ / positiveNormalization 1 (Δ / 2) J)
      (C_T + 1)) 2 ≤ S.n := max_le hnE hn2
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
  obtain ⟨_, _, hcoefficient⟩ := actualCharge_energy_coefficients_of_threshold_le q hCtr hC₁ hC_T
    multiplicity P Cen een hnC Λ T hT R S rfl hmScale hKScale
    hDScale hr hCeq hsize hgraph hdepth hclear hrows hmult
  refine ⟨hK, hKL, hB, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, ?_⟩
  intro E z
  have hd : 0 < E.card := Finset.card_pos.mpr hwindow.2.2.2.2.1
  refine ⟨hwindow, hd, ?_⟩
  have : NeZero E.card := NeZero.of_pos hd
  intro d ΩX ψ Sent dims energy σ near middleRegion gpre gpost gaps gmax tree Gpre Gpost
  have hρ : reducedState Λ q Ωt X =
      Matrix.partialTraceRight (Matrix.vecMulVec ΩX (star ΩX)) :=
    (reducedState_eq_finiteProduct Λ q Ωt X).trans
      (FiniteProduct.reducedPure_eq_partialTrace β Ωt X)
  have hzEq :
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian.spectralRestrictionMass E =
        z := by simp only [← hρ, z]
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
    actualCharges_selection_energy_domainGraph_of_finiteFamilyTransportBound htransport (d := d)
      h Ω S hT hgraph hdepth hanchor hΔ hgs.1 hn2 hrD hDpos hDm
      hKL hCp hCm hrows hmult hclear ha hasmall
  obtain ⟨cU, cL, Cf, hcU, hcL, hCf, hlimU, hlimL, hsharp⟩ :=
    eventually_actualCharge_suppliedPrevector_sharp_comparison hT S hdepth hm hM
      (show 0 < S.K by omega) h Ω Δ L hKL Ωt e (g / 2) htr.1 htr.2.2
      (half_pos hg) a (C₀ * B) _ ha har haone
      (mul_nonneg hC₀.le (zero_le_one.trans hB)) E ell
      hmom hz hpre hmass hdim
  simp only [hzEq, hWa] at hsharp
  obtain ⟨cR, Ci, hcR, hCi, _, hend⟩ :=
    source_actualScan_suppliedPrevector_endpoint_budget_of_threshold_le hq
      (Δ / positiveNormalization 1 (Δ / 2) J) (C_T + 1)
      (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)) hT S hnE hgraph hdepth hm hM a ha
      (show S.r₀ ≤ S.D by omega) hDpos hDm L hKL hrows Ω Ωt hgs.1 htr.1 hcard htrace Ce η
      hsource E ell hz (fun k hk ↦ (hpre k hk).2) hmass
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
  simp only [a, ℓ] at hrate
  have hdensity := selected_density_of_rough_endpoint (rate := rate) hk
    (show 0 < S.n by omega) hm (show 0 < S.D by omega) (show 0 < S.K by omega)
    ha hCp (sub_pos.mpr hp₀₁) hWa cR Ci Cb hendK.2 (hb k) (by
      simpa only [hrate] using hQ)
  have hpInterior : p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hp₀.trans_le hp.1, hp.2.trans_lt hp₁⟩
  have hcoeff := hcoefficient (fun _ ↦ d) J h Ω Δ s.val
    (Nat.succ_le_of_lt s.isLt) W hW.le k pre hsym hnonzero p hpInterior
  have hcap := S.actualCharge_defect_le_of_density_energy_bound hm hM s.val h Ω L
    hΔ W Cen een _ _ P (rem k) e hW.le pre k p henergy hcoeff
  refine ⟨s, p, hp, hdensity, (hsharpK s p).2.1, hcap, ?_⟩
  intro τ hτ hτhalf
  have hmassLoss := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hcap hτ.le) (le_max_left (0 : ℝ) (2 * Sent + gmax))
  have hcomparison := (hsharpK s p).2.2 τ hτ hτhalf
  exact hcomparison.trans
    (_root_.add_le_add (_root_.add_le_add (_root_.add_le_add le_rfl hmassLoss) le_rfl) le_rfl)

open Classical in
/-- The selected actual sharp comparison of
`exists_sourceTarget_selected_actualCharge_sharp_comparison_of_threshold_le` at any transport
constants `ct, C_ent, e_ent, C_en, e_en` satisfying the finite-family transport bound, such as
QICLean's universal transport constants, which depend on none of `q, R, J, Δ`. The transport
smallness threshold is `ct`; only the truncation constant `Ctr` remains existential.
Source: `08-scanner.tex`, lines 400--533 and 839--911. -/
theorem exists_sourceTarget_selected_actualCharge_sharp_comparison_of_finiteFamilyTransportBound
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ)
    {ct Cent eent Cen een : ℝ} (htransport : FiniteFamilyTransportBound ct Cent eent Cen een) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
          (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
          (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
          sourceSelectedSharpThreshold q R Ctr (Δ / positiveNormalization 1 (Δ / 2) J) C₁ C_T
            multiplicity P ≤ S.n →
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
          2 * S.r₀ ≤ S.D → ∀ (_hDpos : 1 ≤ S.D) (_hDm : 4 * S.D ≤ S.m),
          ∃ (hm : 0 < S.m) (hM : 0 < S.M),
          let L := ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
          let δtail := (S.n : ℝ) ^ (-100 : ℝ)
          let B := statusMarginalBudgetConstant q R Ctr *
            ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
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
              targetBudgetConstant q R Ctr * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
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
                        let cap := actualChargeEnergyCoefficient q Ctr multiplicity Cen een *
                          W ^ 2 * (S.n : ℝ) ^ (Exponents.scannerEll : ℝ) * (S.D : ℝ) ^ 2 *
                          (Real.log S.n) ^ transportLogExponent een (een + 1 / 8) *
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
  exact ⟨_, latticeTruncationRadiusConstant_pos R hΔ (by positivity : (0 : ℝ) ≤ C_T + 1),
    sourceTarget_selected_actualCharge_sharp_comparison_explicit hq R hJ hΔ hC_T hC₁ multiplicity
      hmultiplicity P htransport rfl⟩

open Classical in
/-- A single truncated target window and a single physical label sequence produce an actual
selected charge comparison at the literal final scales, at every `S.n` from the explicit
threshold `sourceSelectedSharpThreshold` on. The target and status budget coefficients are
`targetBudgetConstant q R Ctr` and `statusMarginalBudgetConstant q R Ctr`, and the energy cap
has coefficient `actualChargeEnergyCoefficient q Ctr multiplicity Cen een` and logarithmic
exponent `transportLogExponent een (een + 1 / 8)`. The truncation constant `Ctr` and the
transport constants `ct, Cent, eent, Cen, een` remain existential.
Source: `08-scanner.tex`, lines 400--533 and 839--911. -/
theorem exists_sourceTarget_selected_actualCharge_sharp_comparison_of_threshold_le
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ) :
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
          (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
          (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
          sourceSelectedSharpThreshold q R Ctr (Δ / positiveNormalization 1 (Δ / 2) J) C₁ C_T
            multiplicity P ≤ S.n →
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
          2 * S.r₀ ≤ S.D → ∀ (_hDpos : 1 ≤ S.D) (_hDm : 4 * S.D ≤ S.m),
          ∃ (hm : 0 < S.m) (hM : 0 < S.M),
          let L := ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
          let δtail := (S.n : ℝ) ^ (-100 : ℝ)
          let B := statusMarginalBudgetConstant q R Ctr *
            ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
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
              targetBudgetConstant q R Ctr * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
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
                        let cap := actualChargeEnergyCoefficient q Ctr multiplicity Cen een *
                          W ^ 2 * (S.n : ℝ) ^ (Exponents.scannerEll : ℝ) * (S.D : ℝ) ^ 2 *
                          (Real.log S.n) ^ transportLogExponent een (een + 1 / 8) *
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
  exact exists_of_finiteFamilyTransportBound fun _ _ _ _ _ _ htransport ↦
    exists_sourceTarget_selected_actualCharge_sharp_comparison_of_finiteFamilyTransportBound
      hq R hJ hΔ hC_T hC₁ multiplicity hmultiplicity P htransport

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
    ∃ Ctr Ctarget CB ct Cent eent _Cen _een C Cl : ℝ,
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
          2 * S.r₀ ≤ S.D → ∀ (_hDpos : 1 ≤ S.D) (_hDm : 4 * S.D ≤ S.m),
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
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, hall⟩ :=
    exists_sourceTarget_selected_actualCharge_sharp_comparison_of_threshold_le hq R hJ hΔ hC_T
      hC₁ multiplicity hmultiplicity P
  have hcoeff := transport_coefficients_log_bound (NeZero.pos q) hCtr.le
    (10 * (10 * (multiplicity : ℝ)) ^ (7 / 8 : ℝ) * |Cen|) een
    (50 * (multiplicity : ℝ) * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen|) (een + 1 / 8)
  exact ⟨Ctr, _, _, ct, Cent, eent, Cen, een, _, _, hCtr, one_pos.trans_le (le_max_left _ _),
    statusMarginalBudgetConstant_pos q R hCtr.le, hct,
    one_le_mul_of_one_le_of_one_le (by norm_num) hcoeff.1, hcoeff.2.1, _,
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)), hall⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
