/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedDensity
import TNLean.PEPS.AreaLaw.Scan.SelectedEnergyDelta

/-!
# Physical selected density and energy for arbitrary scanner exponents

One truncated target state and one Schmidt--Bell label sequence serve every
admissible total weight. At the same selected charge and interpolation parameter,
the density and energy estimates have common constants and a common logarithmic
power. These constants precede the finite system and the total weight.

The truncation contribution is retained explicitly as a multiple of `n⁻¹⁰⁰⁰`.
The eighth root of the density remainder contributes a separate nonnegative
energy remainder, which tends to zero with the finite system and weight fixed.
The physical norm and projected-mass conclusions remain available for the
norm-comparison clauses of Proposition 9.2.

**Local fix (output constants):** The common density coefficient is enlarged after the input
entropy coefficient is fixed. It need not vanish when the input coefficient is zero. This
distinguishes the two occurrences of the source coefficient; the version with identical
coefficients is not established here. See `docs/paper-gaps/arealaw2d_scanner_inputs.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, Proposition 9.2, `scanner:density-output` and
`scanner:energy-output`, lines 349–397 and 492–533, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

open Classical in
/-- The selected physical charge satisfies the source density and eighth-root
energy estimates with common constants chosen before the finite system and
weight. The original target state, typical set, labels, projected mass, and raw
energy and norm bounds are retained at the same selected interpolation parameter.
The fixed truncation energy and the vanishing replica error remain separate.
Source: Proposition 9.2, `scanner:density-output` and `scanner:energy-output` in
`08-scanner.tex`, lines 349–397 and 492–533. -/
theorem exists_sourceTarget_selected_actualCharge_source_density_energy
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) :
    ∃ Ctr Ctarget c Cent eent _Cen _een : ℝ,
      0 < Ctr ∧ 0 < Ctarget ∧ 0 < c ∧ c ≤ 1 / 2 ∧
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
              e / (g / 2) ≤ Cδ * (S.n : ℝ) ^ (-1000 : ℝ) ∧
              ∃ (b rem ρ ρE : ℕ → ℝ) (Cb cU cR Ci : ℝ),
                0 ≤ Cb ∧ 0 ≤ cU ∧ 0 ≤ cR ∧ 0 ≤ Ci ∧
                (∀ k, 0 ≤ b k) ∧ (∀ k, b k ≤ Cb * Real.log (k + 2)) ∧
                (∀ k, 0 ≤ rem k) ∧ Tendsto rem atTop (𝓝 0) ∧
                (∀ k, 0 ≤ ρ k) ∧ Tendsto ρ atTop (𝓝 0) ∧
                (∀ k, 0 ≤ ρE k) ∧ Tendsto ρE atTop (𝓝 0) ∧
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
                            (1 - p) * (S.n : ℝ) ^ (-100 : ℝ) + p)
                      let normSq := Transport.filteredNormSq
                        ((S.actualChargeData hm hM s.val).rootPath dims (a / 2) k p) (pre k)
                      Q / (S.K * S.n * S.D : ℝ) ≤ δ + ρ k ∧
                      Q / (S.K * S.n * S.D : ℝ) ≤
                        (2 * (S.C₁ + 1) / (W * ((S.n * S.m : ℕ) : ℝ) * (εp / 2))) *
                          (Brough + (2 * S.n * S.m : ℕ) * rate +
                            roughEndpointRemainder d cR S.K
                              (Ci + (2 * S.n * S.m : ℕ) * Cb) k) ∧
                      defect ≤ (e + cap + rem k) / (g / 2) ∧
                      defect ≤ Cδ * W ^ 2 * (S.n : ℝ) ^ F.ell *
                        (S.D : ℝ) ^ 2 * (Real.log S.n) ^ Clδ *
                          (δ ^ (1 / 8 : ℝ) + εp + (S.n : ℝ) ^ (-100 : ℝ)) +
                        Cδ * (S.n : ℝ) ^ (-1000 : ℝ) + ρE k ∧
                      0 < normSq ∧
                      -Real.log normSq / (k : ℝ) ≤
                        Brough + Real.bellOverlapRemainder d cU S.K k := by
  obtain ⟨Ctr, Ctarget, c, Cent, eent, Cen, een,
      hCtr, hCtarget, hc, hchalf, hdensity⟩ :=
    exists_sourceTarget_selected_actualCharge_source_density hq R hJ hΔ hC_T
      hC₁ multiplicity hmultiplicity (100 : ℝ)
  refine ⟨Ctr, Ctarget, c, Cent, eent, Cen, een, hCtr, hCtarget, hc, hchalf,
    fun F ↦ ?_⟩
  obtain ⟨C, Cl, hC, hCl, hdata⟩ := hdensity F
  refine ⟨C, Cl, hC, hCl, fun Ce hCe ↦ ?_⟩
  obtain ⟨Cd, Cld, hCd, hCld, Nb, hNb, hsource⟩ := hdata Ce hCe
  have hgap : 0 < (Δ / positiveNormalization 1 (Δ / 2) J) / 2 :=
    half_pos (div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J))
  obtain ⟨Nl, hlog⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1)
  refine ⟨max Cd ((C + 1) / ((Δ / positiveNormalization 1 (Δ / 2) J) / 2)),
    max Cld Cl, hCd.trans_le (le_max_left _ _), hCld.trans (le_max_left _ _),
    max Nb Nl, hNb.trans (le_max_left _ _), ?_⟩
  intro Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix
  obtain ⟨hrD, hDpos, hDm, hm, hM, hphysical⟩ := hsource Λ T hT h S E₀ Ω hgs
    hgraph hanchor (le_trans (le_max_left _ _) hn) hr hmScale hDScale hKScale hCeq
    hsize hdepth hrows hmult hclear htargetEntropy hprefix
  refine ⟨hrD, hDpos, hDm, hm, hM, ?_⟩
  intro L X β g ε w δtail Bsh
  obtain ⟨hK, hKL, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, hwdata⟩ :=
    hphysical
  refine ⟨hK, hKL, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, ?_⟩
  intro E z
  obtain ⟨hwindow, hd, hpdata⟩ := hwdata
  refine ⟨hwindow, hd, ?_⟩
  have : NeZero E.card := NeZero.of_pos hd
  intro d ΩX ψ Sent dims energy
  obtain ⟨ell, hpre, hmass, hdim, hweights⟩ := hpdata
  refine ⟨ell, hpre, hmass, hdim, ?_⟩
  intro W hW a ℓ hasmall Brough rate
  obtain ⟨hrough, b, rem, ρ, Cb, cU, cR, Ci, hCb, hcU, hcR, hCi, hb0, hb,
      hrem0, hrem, hρ0, hρ, hlimU, hlimR, hpoints⟩ := hweights W hW hasmall
  have hinv : 1 / (g / 2) ≤ max Cd ((C + 1) / (g / 2)) :=
    (div_le_div_of_nonneg_right (by linarith : (1 : ℝ) ≤ C + 1) hgap.le).trans
      (le_max_right _ _)
  have hecap : e / (g / 2) ≤
      max Cd ((C + 1) / (g / 2)) * (S.n : ℝ) ^ (-1000 : ℝ) := by
    calc
      e / (g / 2) ≤ (S.n : ℝ) ^ (-1000 : ℝ) / (g / 2) :=
        div_le_div_of_nonneg_right (he.trans (min_le_left _ _)) hgap.le
      _ = (1 / (g / 2)) * (S.n : ℝ) ^ (-1000 : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hinv (by positivity)
  let A := C * W ^ 2 * (S.n : ℝ) ^ F.ell * (S.D : ℝ) ^ 2 *
    (Real.log S.n) ^ Cl
  have hlogn : 1 ≤ Real.log (S.n : ℝ) := hlog S.n ((le_max_right _ _).trans hn)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans hC) (sq_nonneg W))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _))
    (Real.rpow_nonneg (zero_le_one.trans hlogn) _)
  refine ⟨hrough, hecap, b, rem, ρ,
    (fun k ↦ (A * |ρ k| ^ (1 / 8 : ℝ) + rem k) / (g / 2)),
    Cb, cU, cR, Ci, hCb, hcU, hcR, hCi, hb0, hb, hrem0, hrem, hρ0, hρ,
    (fun k ↦ div_nonneg
      (add_nonneg (mul_nonneg hA (Real.rpow_nonneg (abs_nonneg _) _)) (hrem0 k))
      hgap.le), tendsto_selectedEnergy_remainder hρ hrem A (g / 2), hlimU, hlimR, ?_⟩
  intro εp δ
  have hδmono : F.delta W Cd Cld S.n ≤ δ :=
    mul_le_mul
      (mul_le_mul_of_nonneg_right (le_max_left Cd _)
        (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hlogn (le_max_left Cld Cl))
        (Real.rpow_nonneg (div_nonneg (zero_le_one.trans hW) (Nat.cast_nonneg _)) _)))
      (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg
          (Real.rpow_nonneg (div_nonneg (zero_le_one.trans hW) (Nat.cast_nonneg _)) _)
          (Real.rpow_nonneg (zero_le_one.trans hlogn) _)))
      (mul_nonneg (hCd.le.trans (le_max_left _ _))
        (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have hCgap : C / (g / 2) ≤ max Cd ((C + 1) / (g / 2)) :=
    (div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hgap.le).trans
      (le_max_right _ _)
  have hAcap : A / (g / 2) ≤ max Cd ((C + 1) / (g / 2)) * W ^ 2 *
      (S.n : ℝ) ^ F.ell * (S.D : ℝ) ^ 2 * (Real.log S.n) ^ max Cld Cl := by
    calc
      A / (g / 2) = (C / (g / 2)) * W ^ 2 * (S.n : ℝ) ^ F.ell *
          (S.D : ℝ) ^ 2 * (Real.log S.n) ^ Cl := by dsimp only [A]; ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCgap (sq_nonneg W))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _))
        (Real.rpow_le_rpow_of_exponent_le hlogn (le_max_right Cld Cl))
        (Real.rpow_nonneg (zero_le_one.trans hlogn) _)
        (mul_nonneg
          (mul_nonneg (mul_nonneg (hCd.le.trans (le_max_left _ _)) (sq_nonneg W))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (sq_nonneg _))
  have hδ0 : 0 ≤ δ := le_trans
    (mul_nonneg
      (mul_nonneg hCd.le (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg
          (Real.rpow_nonneg (div_nonneg (zero_le_one.trans hW) (Nat.cast_nonneg _)) _)
          (Real.rpow_nonneg (zero_le_one.trans hlogn) _)))) hδmono
  filter_upwards [hpoints] with k hk
  obtain ⟨s, p, hp, hQ, hQraw, henergy, hnorm, hupper⟩ := hk
  refine ⟨s, p, hp, hQ.trans (_root_.add_le_add hδmono le_rfl), hQraw, henergy,
    ?_, hnorm, hupper⟩
  have hQ0 : 0 ≤ S.actualChargeEntropyDefect hm hM s.val dims energy (a / 2) k
      (replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k) p /
        (S.K * S.n * S.D : ℝ) :=
    div_nonneg (S.actualChargeEntropyDefect_nonneg hm hM s.val dims energy
      (div_nonneg (zero_le_one.trans hW) (Nat.cast_nonneg _)) k
      (fun k ↦ replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k) p)
      (by positivity)
  have hp0 : 0 ≤ p :=
    (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg S.n) (-F.nu)) zero_le_two).trans hp.1
  have hselected := selectedEnergy_le_of_density_le_add (A := A) hQ0 hδ0
    (abs_nonneg (ρ k)) (hQ.trans (_root_.add_le_add hδmono (le_abs_self (ρ k))))
    hgap hA (Real.rpow_nonneg (Nat.cast_nonneg S.n) (-100 : ℝ)) hp0 hp.2 henergy
  exact hselected.trans (_root_.add_le_add (_root_.add_le_add
    (mul_le_mul_of_nonneg_right hAcap
      (add_nonneg (add_nonneg (Real.rpow_nonneg hδ0 _)
        (Real.rpow_nonneg (Nat.cast_nonneg S.n) _))
        (Real.rpow_nonneg (Nat.cast_nonneg S.n) _))) hecap) le_rfl)

end TNLean.PEPS.AreaLaw.Scan.CollarScan
