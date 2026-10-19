/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceChargeSelection
import TNLean.PEPS.AreaLaw.Scan.SelectedDensityDelta
import TNLean.PEPS.AreaLaw.Scan.SubsystemDimensionScale
import TNLean.PEPS.AreaLaw.Scan.ScannerRoundedAdmissibility

/-!
# Physical selected density for arbitrary scanner exponents

The original target and whole-prefix entropy bounds are imposed with the same
exponent before the total metric weight is chosen. One truncated target state,
one typical set, and one label sequence serve every admissible weight `W ≥ 1`.
At the unchanged selected charge and parameter in `[ε / 2, ε]`, the source density
bound is added to the actual energy and rough norm bounds. Its nonnegative
replica remainder tends to zero with the finite physical instance and weight fixed.

The geometric scale inequalities follow from the rounded scales. The only rate
restriction is the source's smallness of `a * r₀²`; no upper growth bound on `W`
or decay condition on the entropy exponent is assumed. The energy estimate still
contains its literal density and the fixed truncation error. This intermediate
result does not assert the final eighth-root energy estimate or the remaining
rough and sharp comparator attachments of Proposition 9.2.

**Local fix (output constants):** The positive density coefficient is chosen after the
input entropy coefficient is fixed. It need not vanish when the input coefficient is zero.
The estimate with numerically identical input and output coefficients is not established
here. See `docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Proposition 9.2, lines 349–397, and the selected-density argument,
lines 475–490, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

open Classical in
/-- The physical scanner satisfies the source density estimate at its same
selected charge and interpolation parameter for every admissible total weight.
The target entropy coefficient precedes the density constants and size threshold;
all these choices precede the finite system and the weight. The same projected
mass, label asymptotics, actual energy and rough upper comparison are retained.
The truncation coefficient is chosen before the local dimension; the remaining
constants may depend on that dimension.
Source: Proposition 9.2, `scanner:entropy-input`, `scanner:density-output`, and
`scanner:selected-density` in `08-scanner.tex`, lines 349–397 and 475–490. -/
theorem exists_sourceTarget_selected_actualCharge_source_density
    (R : ℕ) {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hC_T : 0 ≤ C_T) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (q : ℕ) [NeZero q] (_hq : 1 ≤ q) (C₁ : ℝ) (_hC₁ : 0 < C₁)
        (multiplicity : ℕ) (_hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ),
      ∃ Ctarget c Cent eent _Cen _een : ℝ, 0 < Ctarget ∧ 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ F : ScannerExponents, ∃ C Cl : ℝ, 1 ≤ C ∧ 0 ≤ Cl ∧
        ∀ Ce : ℝ, 0 ≤ Ce →
        ∃ Cδ Clδ : ℝ, 0 < Cδ ∧ 0 ≤ Clδ ∧ ∃ N : ℕ, 2 ≤ N ∧
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
          regionalEntropy Λ q Ω (S.A.filter fun x ↦ x.val ∈ T) ≤
            Ce * (S.n : ℝ) ^ (1 + F.e) →
          (∀ j : ℕ, j ≤ F.L S.n →
            regionalEntropy Λ q Ω (positiveDepthPrefix S.A S.depth (j : ℤ)) ≤
              Ce * ((S.n : ℝ) * (F.L S.n : ℝ) ^ F.e + S.n)) →
          2 * S.r₀ ≤ S.D ∧ 1 ≤ S.D ∧ 4 * S.D ≤ S.m ∧
          ∃ (hm : 0 < S.m) (hM : 0 < S.M),
          let L := F.L S.n
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          let g := Δ / positiveNormalization 1 (Δ / 2) J
          let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
          let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
          let δtail := (S.n : ℝ) ^ (-100 : ℝ)
          let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ F.e + S.n) +
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
              (∀ᶠ k : ℕ in atTop,
                (2 * (((k + 1) ^ (d ^ 2) : ℕ) : ℝ))⁻¹ ≤
                  ‖WithLp.toLp 2
                    (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
                      (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
                      labelProj (copyPerm (Fin d) k) (ell k)) *ᵥ
                      (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                        (Fin k → Fin d) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
              Asymptotics.IsLittleO atTop
                (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) * Sent)
                (fun k : ℕ ↦ (k : ℝ)) ∧
              ∀ W : ℝ, 1 ≤ W →
              let a := W / (S.K : ℝ)
              let ℓ := transportLogDimBound q S.r₀
              a * (S.r₀ : ℝ) ^ 2 ≤ c →
              let Brough := 2 * Real.log (d : ℝ) - Real.log z + W *
                (Bsh / z + (1 + 3 * (S.n : ℝ) * (S.D : ℝ) * Real.log q))
              let rate := Cent * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent
              Brough ≤ (6 * Ce + 13 + 6 * Real.log q) * W *
                (S.n : ℝ) ^ (1 + F.e) ∧
              ∃ (b rem ρ : ℕ → ℝ) (Cb cU cR Ci : ℝ),
                0 ≤ Cb ∧ 0 ≤ cU ∧ 0 ≤ cR ∧ 0 ≤ Ci ∧
                (∀ k, 0 ≤ b k) ∧ (∀ k, b k ≤ Cb * Real.log (k + 2)) ∧
                (∀ k, 0 ≤ rem k) ∧ Tendsto rem atTop (𝓝 0) ∧
                (∀ k, 0 ≤ ρ k) ∧ Tendsto ρ atTop (𝓝 0) ∧
                Tendsto (Real.bellOverlapRemainder d cU S.K) atTop (𝓝 0) ∧
                Tendsto (roughEndpointRemainder d cR S.K
                  (Ci + (2 * S.n * S.m : ℕ) * Cb)) atTop (𝓝 0) ∧
                let εp := F.eps S.n
                let δ := F.delta W Cδ Clδ S.n
                  ∀ᶠ k : ℕ in atTop,
                    ∃ s : Fin (S.n * S.m), ∃ p ∈ Set.Icc (εp / 2) εp,
                      let Q := S.actualChargeEntropyDefect hm hM s.val dims energy
                        (a / 2) k (pre k) p
                      let defect :=
                        ((S.actualChargeScanRound hm hM s.val dims energy a pre).meanEnergy
                          k p - e) /
                          (g / 2)
                      let cap := C * W ^ 2 * (S.n : ℝ) ^ F.ell *
                        (S.D : ℝ) ^ 2 * (Real.log S.n) ^ Cl *
                          ((1 - p) * (Q / (S.K * S.n * S.D : ℝ)) ^ (1 / 8 : ℝ) +
                            (1 - p) * (S.n : ℝ) ^ (-P) + p)
                      let normSq := Transport.filteredNormSq
                        ((S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p) (pre k)
                      Q / (S.K * S.n * S.D : ℝ) ≤ δ + ρ k ∧
                      Q / (S.K * S.n * S.D : ℝ) ≤
                        (2 * (S.C₁ + 1) / (W * ((S.n * S.m : ℕ) : ℝ) * (εp / 2))) *
                          (Brough + (2 * S.n * S.m : ℕ) * rate +
                            roughEndpointRemainder d cR S.K
                              (Ci + (2 * S.n * S.m : ℕ) * Cb) k) ∧
                      defect ≤ (e + cap + rem k) / (g / 2) ∧
                      0 < normSq ∧
                      -Real.log normSq / (k : ℝ) ≤
                        Brough + Real.bellOverlapRemainder d cU S.K k := by
  obtain ⟨Ctr, hCtr, hcore⟩ :=
    exists_sourceTarget_selected_actualCharge_density_energy R hJ hΔ hC_T
  refine ⟨Ctr, hCtr, fun q _ hq C₁ hC₁ multiplicity hmultiplicity P ↦ ?_⟩
  obtain ⟨Ctarget, ct, Cent, eent, Cen, een, hCtarget, hct, hcore⟩ :=
    hcore q hq C₁ hC₁ multiplicity hmultiplicity P
  obtain ⟨c, hc, hsmall⟩ := exists_pos_radius_smallness_threshold hq hct
  refine ⟨Ctarget, min c (1 / 2), Cent, eent, Cen, een, hCtarget,
    lt_min hc (by norm_num), min_le_right _ _, fun F ↦ ?_⟩
  obtain ⟨C, Cl, hC, hCl, Nb, hNb, hsource⟩ := hcore F
  refine ⟨C, Cl, hC, hCl, fun Ce hCe ↦ ?_⟩
  obtain ⟨Ct, Clt, hCt, hClt, hcap⟩ :=
    exists_transport_coefficients_log_bound hq hCtr.le Cent eent Cen een
  obtain ⟨Cscale, Ns, hscale⟩ :=
    (eventually_scaleFacts F).imp fun _ hs ↦ eventually_atTop.mp hs
  obtain ⟨Ng, hNg, hgeom⟩ := F.exists_rounded_admissibility hCtr.le
  obtain ⟨Nt, haux⟩ := eventually_atTop.mp
    ((eventually_one_le_roundedLogRadius hCtr).and
      (((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1).and
        (eventually_abs_regionalEntropy_sub_le_of_truncation q hq
          (Δ / positiveNormalization 1 (Δ / 2) J) (C_T + 1)
          (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)))))
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hq)
  have hCscale : 1 ≤ Cscale := (hscale Ns le_rfl).one_le_C₁
  refine ⟨4 * (C₁ + 1) * (6 * Ce + 13 + 6 * Real.log q + 2 * Ct) * Cscale,
    Clt, by positivity, hClt, max Nb (max Ns (max Ng Nt)),
    hNb.trans (le_max_left _ _), ?_⟩
  intro Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix
  obtain ⟨hrD, hDpos, hDm, hbands, hKL⟩ :
      2 * S.r₀ ≤ S.D ∧ 1 ≤ S.D ∧ 4 * S.D ≤ S.m ∧
        8 ≤ S.K ∧ 8 * S.K * S.m ≤ F.L S.n := by
    simpa only [hr, hmScale, hDScale, hKScale, roundedLogRadius] using
      hgeom S.n (by omega)
  obtain ⟨hm, hM, hdata⟩ := hsource Λ T hT h S E₀ Ω hgs hgraph hanchor (by omega)
    hr hmScale hDScale hKScale hCeq hsize hdepth hrows hmult hclear
    Ce F.e hprefix hrD hDpos hDm
  refine ⟨hrD, hDpos, hDm, hm, hM, ?_⟩
  intro L X β g ε w δtail Bsh
  obtain ⟨hK, hKLcore, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, hwdata⟩ :=
    hdata
  refine ⟨hK, hKLcore, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, ?_⟩
  intro E z
  obtain ⟨hwindow, hd, hpdata⟩ := hwdata
  refine ⟨hwindow, hd, ?_⟩
  have : NeZero E.card := NeZero.of_pos hd
  intro d ΩX ψ Sent dims energy
  have hΩt : ‖Ωt‖ = 1 := (Matrix.isGappedGroundState_iff.mp htrgs).1
  have hcont := (haux S.n (by omega)).2.2 Λ Ω Ωt hgs.1 hΩt X
    ((Nat.cast_le.mpr (Finset.card_le_card hX)).trans hcard) htrace
  have hSt : regionalEntropy Λ q Ωt X ≤
      Ce * (S.n : ℝ) ^ (1 + F.e) + (S.n : ℝ) ^ (-247 : ℝ) := by
    linarith only [le_abs_self (regionalEntropy Λ q Ωt X - regionalEntropy Λ q Ω X),
      hcont, htargetEntropy]
  have hlogd : |Real.log (d : ℝ) - regionalEntropy Λ q Ωt X| ≤ w - Real.log z :=
    (abs_log_card_and_selectedSchmidtEntropy_sub_le Ωt hΩt X E w hwindow.2.2.1
      (fun i hi ↦ (hwindow.2.2.2.2.2 i hi).2)).1
  have hscaleN := hscale S.n (by omega)
  have hceil : (S.D : ℝ) < (S.n : ℝ) ^ F.kappa + 1 := by
    simpa only [hDScale, ScannerExponents.D] using
      Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg S.n) F.kappa)
  have hpower : (S.n : ℝ) ^ F.kappa ≤ (S.n : ℝ) ^ F.e ∧
      1 ≤ (S.n : ℝ) ^ F.e :=
    ⟨Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (by omega)) F.kappa_le_e,
      Real.one_le_rpow (Nat.one_le_cast.mpr (by omega)) F.e_pos.le⟩
  have hDpower : (S.D : ℝ) ≤ 2 * (S.n : ℝ) ^ F.e := by
    linarith only [hceil, hpower.1, hpower.2]
  obtain ⟨ell, hpre, hmass, hdim, hweights⟩ := hpdata
  refine ⟨ell, hpre, hmass, hdim, ?_⟩
  intro W hW a ℓ hasmall Brough rate
  have htransport : a * ℓ ≤ ct :=
    hsmall S.r₀
      (by simpa only [hr, roundedLogRadius] using (haux S.n (by omega)).1)
      a (div_nonneg (zero_le_one.trans hW) (Nat.cast_nonneg _))
      (hasmall.trans (min_le_left _ _))
  have hrough : Brough ≤
      (6 * Ce + 13 + 6 * Real.log q) * W * (S.n : ℝ) ^ (1 + F.e) :=
    roughBudget_le_source_power hscaleN.two_le_n hq F.e_pos.le hCe hW
      hscaleN.L_le_n hDpos hDpower hwindow.2.2.1 hwindow.2.1 hSt hlogd le_rfl
  refine ⟨hrough, ?_⟩
  obtain ⟨b, rem, Cb, cU, cR, Ci,
      hCb, hcU, hcR, hCi, hb0, hb, hrem0, hrem, hlimU, hlimR, hpoints⟩ :=
    hweights W (zero_lt_one.trans_le hW) htransport
  have hℓ1 : 1 ≤ ℓ := by
    dsimp only [ℓ, transportLogDimBound]
    exact le_add_of_nonneg_right (by positivity)
  have hℓcap : ℓ ≤ transportLogDimBound q (roundedLogRadius Ctr S.n) := by
    dsimp only [ℓ, roundedLogRadius]
    rw [hr]
  have hG : Cent * ℓ ^ eent ≤ Ct * Real.log (S.n : ℝ) ^ Clt :=
    (hcap S.n (haux S.n (by omega)).2.1 ℓ hℓ1 hℓcap).1
  have hWa : a * (S.K : ℝ) = W :=
    div_mul_cancel₀ W (Nat.cast_ne_zero.mpr (by omega))
  have hrate : Cent * a * S.K * a ^ (1 / 4 : ℝ) * ℓ ^ eent =
      (Cent * ℓ ^ eent) * W * a ^ (1 / 4 : ℝ) := by
    calc
      _ = (Cent * ℓ ^ eent) * (a * S.K) * a ^ (1 / 4 : ℝ) := by ring
      _ = _ := by rw [hWa]
  let coeff := 2 * (C₁ + 1) /
    (W * ((S.n * S.m : ℕ) : ℝ) * (F.eps S.n / 2))
  let ρ := fun k ↦ |coeff *
    roughEndpointRemainder d cR S.K (Ci + (2 * S.n * S.m : ℕ) * Cb) k|
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    simpa only [ρ, mul_zero, abs_zero] using (hlimR.const_mul coeff).abs
  refine ⟨b, rem, ρ, Cb, cU, cR, Ci, hCb, hcU, hcR, hCi, hb0, hb,
    hrem0, hrem, fun k ↦ abs_nonneg _, hρ, hlimU, hlimR, ?_⟩
  intro εp δ
  have hselected := hpoints (εp / 2) εp (half_pos hscaleN.eps_pos)
    (half_lt_self hscaleN.eps_pos) hscaleN.eps_lt_one
  filter_upwards [hselected] with k hk
  obtain ⟨s, p, hp, hQ, hkeep⟩ := hk
  refine ⟨s, p, hp, ?_,
    by simpa only [show εp - εp / 2 = εp / 2 by ring] using hQ, hkeep⟩
  have hscalar := F.selectedDensity_budget_le_delta hscaleN
    (zero_lt_one.trans_le hW) hC₁ (by positivity : 0 ≤ 6 * Ce + 13 + 6 * Real.log q)
    (zero_le_one.trans hCt) hrough hG
    (R := roughEndpointRemainder d cR S.K (Ci + (2 * S.n * S.m : ℕ) * Cb) k)
  simp only [ScannerExponents.a, ← hmScale, ← hKScale] at hscalar
  simp only [a, ℓ] at hrate
  rw [hrate] at hQ
  exact hQ.trans (by
    simpa only [Brough, δ, ρ, coeff, ℓ, εp, hCeq,
      show εp - εp / 2 = εp / 2 by ring, _root_.mul_assoc] using
      hscalar.trans (_root_.add_le_add le_rfl
        (le_abs_self (coeff * roughEndpointRemainder d cR S.K
          (Ci + (2 * S.n * S.m : ℕ) * Cb) k))))

end TNLean.PEPS.AreaLaw.Scan.CollarScan
