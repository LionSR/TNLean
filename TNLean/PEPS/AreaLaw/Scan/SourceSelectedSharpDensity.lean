/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedSharpComparison
import TNLean.PEPS.AreaLaw.Scan.SelectedDensityPower
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimensionScale
import TNLean.PEPS.AreaLaw.SelectedSchmidtEntropyBounds

/-!
# Source-power density at the same physical sharp-comparison point

The source's original target and whole-row prefix entropy bounds are imposed
before selecting the common truncated target witness and labels. The fixed
entropy coefficient precedes the enlarged size threshold. The existing source
scanner comparison is called once; its actual charge point and all energy and
sharp-comparison conclusions are retained while its density is bounded by the
source power on the literal interval `[n^(-nu), 2*n^(-nu)]`.

The target entropy is transferred using the same trace estimate, and the
selected-dimension estimate uses the same target set. The rounded-scale power
bound and logarithmic transport cap give the principal density estimate.
Only then, for each fixed physical system and total weight, is the replica
remainder taken to zero. No endpoint or small-density estimate is assumed.

Transport smallness and the source geometric separation premises remain
explicit. No entropy telescope, final energy absorption or area law is asserted.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 353–357, 399–533 and 839–911, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter ActualTerminals

open Classical in
/-- The concrete source scanner has an eventually small entropy-defect density
at its unchanged selected charge point, together with the same actual energy
and sharp-comparison bounds. Fixed physical and transport constants precede
the entropy coefficient; that coefficient precedes the size threshold.
The label sequence precedes every admissible weight `1 ≤ W ≤ n^omega`.
Replica thresholds may depend on the fixed physical instance and weight.
Source: `08-scanner.tex`, lines 353–357, 399–533 and 839–911. -/
theorem exists_sourceTarget_selected_actualCharge_sharp_density
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ) :
    ∃ Ctr Ctarget CB ct _Cent _eent _Cen _een C Cl : ℝ,
      0 < Ctr ∧ 0 < Ctarget ∧ 0 < CB ∧ 0 < ct ∧ 1 ≤ C ∧ 0 ≤ Cl ∧
      ∀ Ce : ℝ, 0 ≤ Ce → ∃ N : ℕ, 2 ≤ N ∧
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
          regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ T) ≤
            Ce * (S.n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) →
          (∀ j : ℕ, j ≤ ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ →
            regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
              Ce * ((S.n : ℝ) *
                ((⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊ : ℕ) : ℝ) ^
                  (Exponents.boxError : ℝ) + S.n)) →
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
          let _Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + S.n) +
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
              ∀ W : ℝ, 1 ≤ W → W ≤ (S.n : ℝ) ^ (Exponents.scannerOmega : ℝ) →
                let a := W / (S.K : ℝ)
                let ℓ := transportLogDimBound q S.r₀
                a * ℓ ≤ ct →
                ∃ (b rem : ℕ → ℝ) (Cb cU cL Cf cR Ci : ℝ),
                  0 ≤ Cb ∧ 0 ≤ cU ∧ 0 ≤ cL ∧ 0 ≤ Cf ∧ 0 ≤ cR ∧ 0 ≤ Ci ∧
                  (∀ k, 0 ≤ b k) ∧ (∀ k, b k ≤ Cb * Real.log (k + 2)) ∧
                  (∀ k, 0 ≤ rem k) ∧ Tendsto rem atTop (𝓝 0) ∧
                  Tendsto (Real.bellOverlapRemainder d cU S.K) atTop (𝓝 0) ∧
                  Tendsto (sharpLowerRemainder a cL Cf ell Sent) atTop (𝓝 0) ∧
                  Tendsto (roughEndpointRemainder d cR S.K
                    (Ci + (2 * S.n * S.m : ℕ) * Cb)) atTop (𝓝 0) ∧
                  let εp := (S.n : ℝ) ^ (-(Exponents.scannerNu : ℝ))
                    ∀ᶠ k : ℕ in atTop,
                      ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc εp (2 * εp),
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
                        Q / (S.K * S.n * S.D : ℝ) ≤ εp ∧
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
  obtain ⟨Ctr, Ctarget, CB, ct, Cent, eent, Cen, een, C, Cl,
      hCtr, hCtarget, hCB, hct, hC, hCl, Nb, hNb, hsource⟩ :=
    exists_sourceTarget_selected_actualCharge_sharp_comparison hq R hJ hΔ hC_T
      hC₁ multiplicity hmultiplicity P
  obtain ⟨Ct, Clt, hCt, _, hcap⟩ :=
    exists_transport_coefficients_log_bound hq hCtr.le Cent eent Cen een
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  obtain ⟨Nt, htarget⟩ := eventually_atTop.mp
    (eventually_abs_regionalEntropy_sub_le_of_truncation q hq
      (Δ / positiveNormalization 1 (Δ / 2) J) (C_T + 1) hg)
  obtain ⟨Ni, hinterval⟩ := eventually_atTop.mp
    (eventually_le_natCast_rpow
      (by norm_num [Exponents.scannerNu] : 0 < (Exponents.scannerNu : ℝ)) 4)
  obtain ⟨Nl, hlog⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1)
  refine ⟨Ctr, Ctarget, CB, ct, Cent, eent, Cen, een, C, Cl,
    hCtr, hCtarget, hCB, hct, hC, hCl, ?_⟩
  intro Ce hCe
  obtain ⟨Nd, _, hdensity⟩ := exists_final_selectedDensity_le hq Ce C₁ Ct Clt
    hCe hC₁ (zero_le_one.trans hCt)
  refine ⟨max Nb (max Nd (max Nt (max Ni Nl))), hNb.trans (le_max_left _ _), ?_⟩
  intro Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix hrD hDpos hDm
  have hnB : Nb ≤ S.n := by omega
  have hnD : Nd ≤ S.n := by omega
  have hnT : Nt ≤ S.n := by omega
  have hnI : Ni ≤ S.n := by omega
  have hnLog : Nl ≤ S.n := by omega
  obtain ⟨hm, hM, hdata⟩ := hsource Λ T hT h S E₀ Ω hgs hgraph hanchor hnB
    hr hmScale hDScale hKScale hCeq hsize hdepth hrows hmult hclear
    Ce (Exponents.boxError : ℝ) hprefix hrD hDpos hDm
  refine ⟨hm, hM, ?_⟩
  intro L X β g ε w δtail B C₀ Bsh
  obtain ⟨hK, hKL, hB, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, hwdata⟩ :=
    hdata
  refine ⟨hK, hKL, hB, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, ?_⟩
  intro E z
  obtain ⟨hwindow, hd, hpdata⟩ := hwdata
  refine ⟨hwindow, hd, ?_⟩
  have : NeZero E.card := NeZero.of_pos hd
  intro d ΩX ψ Sent dims energy σ near middleRegion gpre gpost gaps gmax tree Gpre Gpost
  have hΩt : ‖Ωt‖ = 1 := (Matrix.isGappedGroundState_iff.mp htrgs).1
  have hXcard : (X.card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 :=
    (Nat.cast_le.mpr (Finset.card_le_card hX)).trans hcard
  have hcont := htarget S.n hnT Λ Ω Ωt hgs.1 hΩt X hXcard htrace
  have hSt : regionalEntropy Λ q Ωt X ≤
      Ce * (S.n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) +
        (S.n : ℝ) ^ (-247 : ℝ) := by
    have h := le_abs_self (regionalEntropy Λ q Ωt X - regionalEntropy Λ q Ω X)
    linarith
  have hlogd : |Real.log (d : ℝ) - regionalEntropy Λ q Ωt X| ≤ w - Real.log z :=
    (abs_log_card_and_selectedSchmidtEntropy_sub_le Ωt hΩt X E w hwindow.2.2.1
      (fun i hi ↦ (hwindow.2.2.2.2.2 i hi).2)).1
  obtain ⟨ell, hpre, hdim, hweights⟩ := hpdata
  refine ⟨ell, ?_⟩
  intro pre
  refine ⟨hpre, hdim, ?_⟩
  intro W hW hWupper a ℓ hasmall
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  obtain ⟨b, rem, Cb, cU, cL, Cf, cR, Ci,
      hCb, hcU, hcL, hCf, hcR, hCi, hb0, hb, hrem0, hrem, hlimU, hlimL,
      hlimR, hpoints⟩ := hweights W hWpos hWupper hasmall
  refine ⟨b, rem, Cb, cU, cL, Cf, cR, Ci,
    hCb, hcU, hcL, hCf, hcR, hCi, hb0, hb, hrem0, hrem, hlimU, hlimL, hlimR, ?_⟩
  intro εp
  have hnpos : (0 : ℝ) < S.n := by exact_mod_cast (show 0 < S.n by omega)
  have hεp : 0 < εp := Real.rpow_pos_of_pos hnpos _
  have hεp2 : 2 * εp < 1 := by
    have hpow := hinterval S.n hnI
    have hid : εp * (S.n : ℝ) ^ (Exponents.scannerNu : ℝ) = 1 := by
      dsimp only [εp]
      rw [← Real.rpow_add hnpos, neg_add_cancel, Real.rpow_zero]
    nlinarith [mul_le_mul_of_nonneg_left hpow hεp.le]
  have hℓ1 : 1 ≤ ℓ := by
    have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
    dsimp only [ℓ, transportLogDimBound]
    exact le_add_of_nonneg_right (by positivity)
  have hℓcap : ℓ ≤ transportLogDimBound q (roundedLogRadius Ctr S.n) := by
    dsimp only [ℓ, roundedLogRadius]
    rw [hr]
  have hG : Cent * ℓ ^ eent ≤ Ct * Real.log (S.n : ℝ) ^ Clt :=
    (hcap S.n (hlog S.n hnLog) ℓ hℓ1 hℓcap).1
  have hclosure := hdensity S.n hnD
  simp only [← hmScale, ← hDScale, ← hKScale] at hclosure
  apply hclosure W hW hWupper (regionalEntropy Λ q Ωt X) (Real.log (d : ℝ)) z Bsh
    (Cent * ℓ ^ eent) hwindow.2.2.1 hwindow.2.1 hSt hlogd le_rfl hG
    (roughEndpointRemainder d cR S.K (Ci + (2 * S.n * S.m : ℕ) * Cb)) hlimR
  have hselected := hpoints εp (2 * εp) hεp (by linarith) hεp2
  filter_upwards [hselected] with k hk
  obtain ⟨s, p, hp, hQ, hkeep⟩ := hk
  refine ⟨s, p, hp, ?_, hkeep⟩
  have hKr : (0 : ℝ) < S.K := by exact_mod_cast (show 0 < S.K by omega)
  have hWa : a * (S.K : ℝ) = W := div_mul_cancel₀ W hKr.ne'
  have hrate : Cent * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent =
      (Cent * ℓ ^ eent) * W * a ^ (1 / 4 : ℝ) := by
    calc
      _ = (Cent * ℓ ^ eent) * (a * S.K) * a ^ (1 / 4 : ℝ) := by ring
      _ = _ := by rw [hWa]
  simp only [a, ℓ] at hrate
  rw [hrate] at hQ
  simpa only [hCeq, show 2 * εp - εp = εp by ring,
    _root_.mul_assoc] using hQ

end TNLean.PEPS.AreaLaw.Scan.CollarScan
