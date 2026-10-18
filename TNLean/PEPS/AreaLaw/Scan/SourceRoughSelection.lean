/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TargetTypicalWindow
import TNLean.PEPS.AreaLaw.Scan.BandCountGrowth
import TNLean.PEPS.AreaLaw.Scan.ActualRoughLowerPrevector
import TNLean.PEPS.AreaLaw.Scan.GenericSelectedChargeEnergy
import TNLean.PEPS.AreaLaw.Scan.SourceEndpointRoughBudget
import TNLean.PEPS.AreaLaw.Scan.RoughSelectionBudget
import TNLean.PEPS.AreaLaw.GlobalSchmidtBellPrevector

/-!
# A rough-only physical source selection at arbitrary scanner exponents

The target-window theorem is invoked once at arbitrary fixed source scanner
exponents. Its original-state prefix input transfers to that same truncated
vector. One physical Schmidt--Bell label sequence then supplies both the
actual endpoint budget and a rough norm upper bound at every selected point.
The literal selector and generic actual energy coefficients give the density
and normalized-energy estimates with their fixed-instance replica remainders.

There is no sharp moment interval, growing-weight upper bound, or supplied
low-energy conclusion. The total metric weight is four. This supplies the
physical source of the rough bootstrap, not its entropy absorption or the
one-step safe-box conclusion.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 130--166, 240--281 and 332--381;
`08-scanner.tex`, lines 399--533 and 693--769, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.

Validation and inherited-dependency scope:
`docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

/-- The explicit threshold of the rough-only physical source selection at scanner exponents
`F`: the target-window threshold, the actual charge-energy threshold, the prefix-entropy
continuity threshold `truncationEntropyThreshold q g (C_T + 1)`, and the threshold for at least
eight bands (`08-scanner.tex`, lines 399--533 and 693--769). -/
noncomputable def _root_.TNLean.PEPS.AreaLaw.Scan.ScannerExponents.sourceRoughSelectionThreshold
    (F : ScannerExponents) (q R : ℕ) (Ctr g C₁ C_T : ℝ) (multiplicity : ℕ) (P : ℝ) : ℕ :=
  max (targetTypicalWindowThreshold q R Ctr g)
    (max (F.actualChargeEnergyThreshold Ctr C₁ C_T multiplicity P)
      (max (truncationEntropyThreshold q g (C_T + 1)) (F.bandCountThreshold 8)))

open Classical in
/-- At arbitrary fixed scanner exponents and total weight four, one actual target-window vector
and one physical label sequence give a selected density, its actual energy cap, and both rough
comparisons at the same selected point, at every `S.n` from the explicit threshold
`F.sourceRoughSelectionThreshold` on. The target-budget coefficient is
`targetBudgetConstant q R Ctr`, and the energy cap has coefficient
`actualChargeEnergyCoefficient q Ctr multiplicity Cen een` and logarithmic exponent
`transportLogExponent een (een + 1 / 8)`. The truncation constant `Ctr` and the transport
constants `ct, Cent, eent, Cen, een` remain existential. Source: `08-scanner.tex`,
lines 399--533 and 693--769. -/
theorem exists_sourceTarget_selected_actualCharge_rough_comparison_of_threshold_le
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ) :
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
      ∀ F : ScannerExponents,
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
          (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
          (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
          F.sourceRoughSelectionThreshold q R Ctr (Δ / positiveNormalization 1 (Δ / 2) J) C₁ C_T
            multiplicity P ≤ S.n →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          S.m = F.m S.n → S.D = F.D S.n → S.K = F.K S.n →
          S.C₁ = C₁ → (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ r : ℕ, 1 ≤ r → r ≤ F.L S.n →
            (ambientDilation T r \ ambientDilation T (r - 1)).card ≤ S.n) →
          (∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ multiplicity) →
          (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
            ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
          ∀ Ce η : ℝ,
          (∀ j : ℕ, j ≤ F.L S.n →
            regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
              Ce * ((S.n : ℝ) * (F.L S.n : ℝ) ^ η + S.n)) →
          2 * S.r₀ ≤ S.D → ∀ (_hDpos : 1 ≤ S.D) (_hDm : 4 * S.D ≤ S.m),
          ∃ (hm : 0 < S.m) (hM : 0 < S.M),
          let L := F.L S.n
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
          let δtail := (S.n : ℝ) ^ (-100 : ℝ)
          let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ η + S.n) +
            (S.n : ℝ) ^ (-247 : ℝ)
          8 ≤ S.K ∧ 8 * S.K * S.m ≤ L ∧
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
              let a := 4 / (S.K : ℝ)
              let ℓ := transportLogDimBound q S.r₀
              a * ℓ ≤ ct →
              let Brough := 2 * Real.log (d : ℝ) - Real.log z + 4 *
                (Bsh / z + (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log q))
              let rate := Cent * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent
              ∃ (b rem : ℕ → ℝ) (Cb cU cR Ci cL Cf : ℝ),
                0 ≤ Cb ∧ 0 ≤ cU ∧ 0 ≤ cR ∧ 0 ≤ Ci ∧ 0 ≤ cL ∧ 0 ≤ Cf ∧
                (∀ k, 0 ≤ b k) ∧ (∀ k, b k ≤ Cb * Real.log (k + 2)) ∧
                (∀ k, 0 ≤ rem k) ∧ Tendsto rem atTop (𝓝 0) ∧
                Tendsto (Real.bellOverlapRemainder d cU S.K) atTop (𝓝 0) ∧
                Tendsto (roughEndpointRemainder d cR S.K
                  (Ci + (2 * S.n * S.m : ℕ) * Cb)) atTop (𝓝 0) ∧
                Tendsto (roughLowerRemainder S.K cL Cf ell Sent) atTop (𝓝 0) ∧
                ∀ p₀ p₁ : ℝ, 0 < p₀ → p₀ < p₁ → p₁ < 1 →
                  ∀ᶠ k : ℕ in atTop,
                    ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc p₀ p₁,
                      let Q := S.actualChargeEntropyDefect hm hM s.val dims energy
                        (a / 2) k (pre k) p
                      let defect :=
                        ((S.actualChargeScanRound hm hM s.val dims energy a pre).meanEnergy
                          k p - e) /
                          (g / 2)
                      let cap := actualChargeEnergyCoefficient q Ctr multiplicity Cen een *
                        (4 : ℝ) ^ 2 * (S.n : ℝ) ^ F.ell * (S.D : ℝ) ^ 2 *
                        (Real.log S.n) ^ transportLogExponent een (een + 1 / 8) *
                          ((1 - p) * (Q / (S.K * S.n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                            (1 - p) * (S.n : ℝ) ^ (-P) + p)
                      let normSq := Transport.filteredNormSq
                        ((S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p) (pre k)
                      Q / (S.K * S.n * S.D : ℝ) ≤
                        (2 * (S.C₁ + 1) / (4 * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀))) *
                          (Brough + (2 * S.n * S.m : ℕ) * rate +
                            roughEndpointRemainder d cR S.K
                              (Ci + (2 * S.n * S.m : ℕ) * Cb) k) ∧
                      0 ≤ defect ∧ defect ≤ (e + cap + rem k) / (g / 2) ∧
                      0 < normSq ∧
                      -Real.log normSq / (k : ℝ) ≤
                        Brough + Real.bellOverlapRemainder d cU S.K k ∧
                      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                        4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
                          3 * (defect / τ) * max 0 (2 * Sent) -
                            roughLowerRemainder S.K cL Cf ell Sent k ≤
                              -Real.log normSq / (k : ℝ) := by
  classical
  obtain ⟨ct, Cent, eent, Cen, een, hct, hselector⟩ :=
    actualCharges_selection_energy_domainGraph
  obtain ⟨Ctr, hCtr, hwindow⟩ :=
    exists_truncated_target_typical_window_of_targetTypicalWindowThreshold_le R hJ hΔ hC_T
  have htarget := hwindow q hq
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hprefix := fun n (hn : truncationEntropyThreshold q
      (Δ / positiveNormalization 1 (Δ / 2) J) (C_T + 1) ≤ n) =>
    regionalEntropy_positiveDepthPrefix_le_of_truncationEntropyThreshold_le q hq
      (Δ / positiveNormalization 1 (Δ / 2) J) (C_T + 1) hg hn
  refine ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, ?_⟩
  intro F Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear Ce η hsource hrD hDpos hDm
  simp only [ScannerExponents.sourceRoughSelectionThreshold, max_le_iff] at hn
  obtain ⟨hnT, hnC, hnE, hnS⟩ := hn
  have hn2 : 2 ≤ S.n := (le_max_left _ _).trans hnT
  have hCp : 0 < S.C₁ := hCeq.symm ▸ hC₁
  have hCm : 3 * (multiplicity : ℝ) ≤ S.C₁ := hCeq.symm ▸ hmultiplicity
  let hm : 0 < S.m := by omega
  let hM : 0 < S.M := chargeSlotCount_pos hCp (le_trans (by decide) hn2) hDpos
  refine ⟨hm, hM, ?_⟩
  intro L X β g ε w δtail Bsh
  have hK8 : 8 ≤ S.K := hKScale.symm ▸ F.le_K_of_bandCountThreshold_le 8 hnS
  have hK : 1 ≤ S.K := by omega
  have hKL : 8 * S.K * S.m ≤ L := by
    rw [hKScale, hmScale]
    simpa only [ScannerExponents.K, mul_comm, mul_left_comm, _root_.mul_assoc] using
      Nat.div_mul_le_self (F.L S.n) (8 * F.m S.n)
  have hKScale' : S.K = F.L S.n / (8 * S.m) := by
    simpa only [ScannerExponents.K, ← hmScale] using hKScale
  obtain ⟨hcard, hX, _, e, Ωt, htrgs, he0, he, _, htrace, _, _, hBX, htail,
      hwindow⟩ :=
    htarget Λ h S E₀ Ω F T hT hgs hgraph hanchor hnT hr hsize hdepth hrows hclear
  obtain ⟨_, _, hcoefficient⟩ := F.actualCharge_energy_coefficients_of_threshold_le q hCtr hC₁
    hC_T multiplicity P Cen een hnC Λ T hT R S rfl hmScale hKScale'
    hDScale hr hCeq hsize hgraph hdepth hclear hrows hmult
  refine ⟨hK8, hKL, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, ?_⟩
  intro E z
  have hd : 0 < E.card := Finset.card_pos.mpr hwindow.2.2.2.2.1
  refine ⟨hwindow, hd, ?_⟩
  have : NeZero E.card := NeZero.of_pos hd
  intro d ΩX ψ Sent dims energy
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
  intro a ℓ hasmall Brough rate
  have hKr : (0 : ℝ) < S.K := by exact_mod_cast (show 0 < S.K by omega)
  have ha : 0 < a := div_pos (by norm_num) hKr
  have hWa : a * (S.K : ℝ) = 4 := div_mul_cancel₀ _ hKr.ne'
  have hsh : ∀ j : Fin (L + 1),
      FiniteProduct.entropy β Ωt (positiveDepthPrefix S.A S.depth (j.val : ℤ)) ≤ Bsh := by
    intro j
    simpa only [regionalEntropy_eq_finiteProduct] using
      hprefix S.n hnE Λ Ω Ωt hgs.1 htr.1 S.A S.depth L hcard htrace
        Ce η hsource j.val (Nat.le_of_lt_succ j.isLt)
  obtain ⟨cU, hcU, hlimU, hupper⟩ :=
    eventually_actualScan_suppliedPrevector_rough_upper hT S hgraph hdepth hm hM a ha
      (show 0 < S.n by omega) (show S.r₀ ≤ S.D by omega) hDpos hDm L hKL hrows
      Ωt htr.1 E ell Bsh hsh hz hmass
  simp only [hzEq, hWa] at hupper
  obtain ⟨cR, Ci, hcR, hCi, _, hend⟩ :=
    eventually_actualScan_suppliedPrevector_endpoint_budget hT S hgraph hdepth hm hM a ha
      (show 0 < S.n by omega) (show S.r₀ ≤ S.D by omega) hDpos hDm L hKL hrows
      Ωt htr.1 E ell Bsh hsh hz (fun k hk ↦ (hpre k hk).2) hmass
  simp only [hzEq, hWa] at hend
  obtain ⟨b, rem, Cb, hCb, hb0, hb, hrem0, hrem, hselect⟩ :=
    hselector (d := d) h Ω S hT hgraph hdepth hanchor hΔ hgs.1 hn2 hrD hDpos hDm
      hKL hCp hCm hrows hmult hclear ha hasmall
  obtain ⟨cL, Cf, hcL, hCf, hlower⟩ :=
    exists_actualScan_suppliedPrevector_rough_lower
      (Λ := Λ) (q := q) (d := d) (R := R) (J := J) S.K hK8
  obtain ⟨hlimL, hlower⟩ :=
    hlower S rfl hm hM h Ω Δ L Ωt e (g / 2) htr.1 htr.2.2 (half_pos hg)
      ell Sent hpre hdim
  refine ⟨b, rem, Cb, cU, cR, Ci, cL, Cf, hCb, hcU, hcR, hCi, hcL, hCf,
    hb0, hb, hrem0, hrem, hlimU,
    tendsto_roughEndpointRemainder d cR S.K (Ci + (2 * S.n * S.m : ℕ) * Cb), hlimL, ?_⟩
  intro p₀ p₁ hp₀ hp₀₁ hp₁
  filter_upwards [hupper, hend, eventually_gt_atTop 0] with k hupperK hendK hk
  obtain ⟨hnonzero, hsym, heigen⟩ := augmented_prevector_properties_of_global
    q d k Ωt (ell k) (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e
      (hphysical k hk).1 (hphysical k hk).2.2.1
  obtain ⟨s, p, hp, hQ, henergy⟩ :=
    hselect pre k hk hsym hnonzero e heigen p₀ p₁ hp₀ hp₀₁ hp₁
  have hrate : Cent * (k : ℝ) * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent =
      (k : ℝ) * rate := by dsimp only [rate]; ring
  simp only [ℓ] at hrate
  have hdensity := selected_density_of_rough_endpoint (rate := rate) hk
    (show 0 < S.n by omega) hm (show 0 < S.D by omega) (show 0 < S.K by omega)
    ha hCp (sub_pos.mpr hp₀₁) hWa cR Ci Cb hendK.2 (hb k) (by
      simpa only [hrate] using hQ)
  have hpInterior : p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hp₀.trans_le hp.1, hp.2.trans_lt hp₁⟩
  have hcoeff := hcoefficient (fun _ ↦ d) J h Ω Δ s.val
    (Nat.succ_le_of_lt s.isLt) 4 (by norm_num) k pre hsym hnonzero p hpInterior
  have hcap := S.actualCharge_defect_le_of_density_energy_bound_at_exponent
    hm hM s.val h Ω L hΔ F.ell 4 Cen een _ _ P (rem k) e (by norm_num)
    pre k p henergy hcoeff
  have hlowerCharge := (hlower k hk s p).2.2
  exact ⟨s, p, hp, hdensity, hlowerCharge.2.1, hcap, hlowerCharge.1,
    (hupperK s.val (Nat.succ_le_of_lt s.isLt) p).2.2, hlowerCharge.2.2⟩

open Classical in
/-- At arbitrary fixed scanner exponents and total weight four, one actual
target-window vector and one physical label sequence give a selected density,
its actual energy cap, and both rough comparisons at the same selected point.
All outer constants and thresholds precede the physical instance. Source:
`08-scanner.tex`, lines 399--533 and 693--769. -/
theorem exists_sourceTarget_selected_actualCharge_rough_comparison
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ) :
    ∃ Ctr Ctarget ct Cent eent _Cen _een : ℝ,
      0 < Ctr ∧ 0 < Ctarget ∧ 0 < ct ∧
      ∀ F : ScannerExponents, ∃ C Cl : ℝ, 1 ≤ C ∧ 0 ≤ Cl ∧
        ∃ N : ℕ, 2 ≤ N ∧
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
          (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
          (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) → N ≤ S.n →
          S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
          S.m = F.m S.n → S.D = F.D S.n → S.K = F.K S.n →
          S.C₁ = C₁ → (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
          S.depth = (fun x ↦ ambientDepth T hT x.val) →
          (∀ r : ℕ, 1 ≤ r → r ≤ F.L S.n →
            (ambientDilation T r \ ambientDilation T (r - 1)).card ≤ S.n) →
          (∀ x, (Finset.univ.filter fun i ↦ S.anchor i = x).card ≤ multiplicity) →
          (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
            ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
          ∀ Ce η : ℝ,
          (∀ j : ℕ, j ≤ F.L S.n →
            regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
              Ce * ((S.n : ℝ) * (F.L S.n : ℝ) ^ η + S.n)) →
          2 * S.r₀ ≤ S.D → ∀ (_hDpos : 1 ≤ S.D) (_hDm : 4 * S.D ≤ S.m),
          ∃ (hm : 0 < S.m) (hM : 0 < S.M),
          let L := F.L S.n
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
          let δtail := (S.n : ℝ) ^ (-100 : ℝ)
          let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ η + S.n) +
            (S.n : ℝ) ^ (-247 : ℝ)
          8 ≤ S.K ∧ 8 * S.K * S.m ≤ L ∧
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
              let a := 4 / (S.K : ℝ)
              let ℓ := transportLogDimBound q S.r₀
              a * ℓ ≤ ct →
              let Brough := 2 * Real.log (d : ℝ) - Real.log z + 4 *
                (Bsh / z + (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log q))
              let rate := Cent * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent
              ∃ (b rem : ℕ → ℝ) (Cb cU cR Ci cL Cf : ℝ),
                0 ≤ Cb ∧ 0 ≤ cU ∧ 0 ≤ cR ∧ 0 ≤ Ci ∧ 0 ≤ cL ∧ 0 ≤ Cf ∧
                (∀ k, 0 ≤ b k) ∧ (∀ k, b k ≤ Cb * Real.log (k + 2)) ∧
                (∀ k, 0 ≤ rem k) ∧ Tendsto rem atTop (𝓝 0) ∧
                Tendsto (Real.bellOverlapRemainder d cU S.K) atTop (𝓝 0) ∧
                Tendsto (roughEndpointRemainder d cR S.K
                  (Ci + (2 * S.n * S.m : ℕ) * Cb)) atTop (𝓝 0) ∧
                Tendsto (roughLowerRemainder S.K cL Cf ell Sent) atTop (𝓝 0) ∧
                ∀ p₀ p₁ : ℝ, 0 < p₀ → p₀ < p₁ → p₁ < 1 →
                  ∀ᶠ k : ℕ in atTop,
                    ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc p₀ p₁,
                      let Q := S.actualChargeEntropyDefect hm hM s.val dims energy
                        (a / 2) k (pre k) p
                      let defect :=
                        ((S.actualChargeScanRound hm hM s.val dims energy a pre).meanEnergy
                          k p - e) /
                          (g / 2)
                      let cap := C * (4 : ℝ) ^ 2 * (S.n : ℝ) ^ F.ell *
                        (S.D : ℝ) ^ 2 * (Real.log S.n) ^ Cl *
                          ((1 - p) * (Q / (S.K * S.n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                            (1 - p) * (S.n : ℝ) ^ (-P) + p)
                      let normSq := Transport.filteredNormSq
                        ((S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p) (pre k)
                      Q / (S.K * S.n * S.D : ℝ) ≤
                        (2 * (S.C₁ + 1) / (4 * ((S.n * S.m : ℕ) : ℝ) * (p₁ - p₀))) *
                          (Brough + (2 * S.n * S.m : ℕ) * rate +
                            roughEndpointRemainder d cR S.K
                              (Ci + (2 * S.n * S.m : ℕ) * Cb) k) ∧
                      0 ≤ defect ∧ defect ≤ (e + cap + rem k) / (g / 2) ∧
                      0 < normSq ∧
                      -Real.log normSq / (k : ℝ) ≤
                        Brough + Real.bellOverlapRemainder d cU S.K k ∧
                      ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                        4 * Sent - 6 * (τ * Real.log (d : ℝ) + Real.binEntropy τ / a) -
                          3 * (defect / τ) * max 0 (2 * Sent) -
                            roughLowerRemainder S.K cL Cf ell Sent k ≤
                              -Real.log normSq / (k : ℝ) := by
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, hall⟩ :=
    exists_sourceTarget_selected_actualCharge_rough_comparison_of_threshold_le hq R hJ hΔ hC_T
      hC₁ multiplicity hmultiplicity P
  have hcoeff := transport_coefficients_log_bound (NeZero.pos q) hCtr.le
    (10 * (10 * (multiplicity : ℝ)) ^ (7 / 8 : ℝ) * |Cen|) een
    (50 * (multiplicity : ℝ) * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen|) (een + 1 / 8)
  exact ⟨Ctr, _, ct, Cent, eent, Cen, een, hCtr, one_pos.trans_le (le_max_left _ _), hct,
    fun F => ⟨_, _, one_le_mul_of_one_le_of_one_le (by norm_num) hcoeff.1, hcoeff.2.1, _,
      (le_max_left _ _).trans (le_max_left _ _), hall F⟩⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan

