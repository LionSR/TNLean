/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.ActualSharpUpper
import TNLean.PEPS.AreaLaw.Scan.TargetTypicalWindow
import TNLean.PEPS.AreaLaw.Scan.StatusScaleSeparation
import TNLean.PEPS.AreaLaw.Scan.SharpMomentScale

/-!
# The actual sharp upper estimate at the source target scales

One target-window construction supplies the truncated physical ground vector,
its target spectral restriction, and the quantitative energy, phase and trace
estimates. Geometric status budgets supply the common marginal moments of that
same vector. The literal rounded scales and an explicit positive exponent
margin place six times the per-band weight in the common moment interval.

The truncation, target-budget and status-budget constants precede the scanner
exponents and every physical instance. The integer threshold may depend on the
fixed exponent margin. The supplied label sequence uses the same physical
spectral restriction throughout the actual fill and charge estimates.

The hypothesis
`ω + (1 + F.kappa) / 2 < 1 - F.ell - F.mu` is stronger than the ordinary
scanner exponent assumptions. The vanishing replica remainder concerns each
fixed physical instance. The full Proposition 9.6 lower estimate, telescope
and absorption are not asserted here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, `comparator:sharp-upper`, lines 383–418;
`08-scanner.tex`, lines 32–58, 400–474 and 859–865, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter ActualTerminals

open Classical in
/-- The source target window and common physical status moments give the actual
sharp upper estimate for every supplied label sequence with the physical mass
bound. There is one truncated vector and one target set. The same fixed
physical instance has a remainder tending to zero, uniformly over scan times
and interpolation parameters.

The strict margin is explicit: ordinary scanner exponents alone do not imply
it. The number of bands retains its natural-number division, the collar and
history lengths retain their floors, and the separation retains its ceiling.
Source: `07-comparators.tex`, `comparator:sharp-upper`, lines 383–418;
`08-scanner.tex`, lines 32–58, 400–474 and 859–865. -/
theorem exists_truncated_target_actualSharpUpper {q : ℕ} [NeZero q]
    (hq : 1 ≤ q) (R : ℕ) {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) :
    ∃ Ctr Ctarget CB : ℝ, 0 < Ctr ∧ 0 < Ctarget ∧ 0 < CB ∧
      ∀ (F : ScannerExponents) (ω : ℝ),
        ω + (1 + F.kappa) / 2 < 1 - F.ell - F.mu →
        ∃ N : ℕ, 2 ≤ N ∧
          ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
            (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
            (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
            (hM : 0 < S.M) (E₀ : ℝ) (Ω : StateSpace Λ q),
            IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) → N ≤ S.n →
            S.r₀ = ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ →
            S.m = ⌊(S.n : ℝ) ^ F.mu⌋₊ →
            S.D = ⌈(S.n : ℝ) ^ F.kappa⌉₊ →
            S.K = F.L S.n / (8 * S.m) →
            (T.card : ℝ) ≤ C_T * (S.n : ℝ) ^ 2 →
            S.depth = (fun x ↦ ambientDepth T hT x.val) →
            (∀ d : ℕ, 1 ≤ d → d ≤ F.L S.n →
              (ambientDilation T d \ ambientDilation T (d - 1)).card ≤ S.n) →
            (∀ t ∈ T, ∀ z ∈ Geometry.boundaryEndpoints Λ S.A,
              ((2 * F.L S.n + 10 * S.r₀ : ℕ) : ℤ) < ambientSupDistance t z) →
            let L := F.L S.n
            let X := S.A.filter fun x ↦ x.val ∈ T
            let g := Δ / positiveNormalization 1 (Δ / 2) J
            let ε := min ((S.n : ℝ) ^ (-1000 : ℝ)) (g / 4)
            let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
            let δ := (S.n : ℝ) ^ (-100 : ℝ)
            let B := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
            let C₀ := 512 * Real.exp 1 * (2 / g)
            let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
            1 ≤ S.K ∧ 1 ≤ B ∧ 0 < C₀ ∧ 0 < c₀ ∧
            ((S.truncationSet L).card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 ∧
            X ⊆ S.truncationSet L ∧ (edgeBoundary Λ X).card ≤ 4 * S.n ∧
            ∃ (e : ℝ) (Ωt : StateSpace Λ q),
              IsGappedGroundState Λ q (∑ i, S.truncatedEnergyTerm h Ω Δ L i) e Ωt (g / 2) ∧
              0 ≤ e ∧ e ≤ ε ∧
              (∃ θ : ℝ, ‖Ωt - Complex.exp (θ * Complex.I) • Ω‖ ≤
                2 * Real.sqrt (ε / g)) ∧
              Matrix.traceDistance
                  (Matrix.vecMulVec (WithLp.ofLp Ωt) (star (WithLp.ofLp Ωt)))
                  (Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
                Real.sqrt (2 * ε / g) ∧
              (∀ (Y : Finset (Site Λ)) (u : ℝ),
                |u| ≤ Entropy.tailRadius (2 / g)
                  (cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Y) →
                Real.log (Entropy.surprisalMoment
                  (reducedState_isHermitian Λ q Ωt Y).eigenvalues u) ≤
                    u * regionalEntropy Λ q Ωt Y +
                      C₀ * cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Y * u ^ 2) ∧
              (∀ (Y : Finset (Site Λ)) (v : ℝ),
                Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt Y).eigenvalues
                  (regionalEntropy Λ q Ωt Y) v ≤
                    min 1 (2 * Real.exp (Real.exp 1 / 2) *
                      Real.exp (-(v / (32 * Real.sqrt ((1 + 2 / g) *
                        cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor Y)))))) ∧
              cutBudget q S.graph (S.truncationSet L) S.r₀ S.anchor X ≤
                Ctarget * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
              Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
                (regionalEntropy Λ q Ωt X) w ≤ δ ∧
              let p := (reducedState_isHermitian Λ q Ωt X).eigenvalues
              let E := Entropy.typicalSet p (regionalEntropy Λ q Ωt X) w
              let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
              (0 < 1 - δ ∧ 1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
                ∀ i ∈ E, 0 < p i ∧
                  Real.exp (-regionalEntropy Λ q Ωt X - w) ≤ p i ∧
                  p i ≤ Real.exp (-regionalEntropy Λ q Ωt X + w)) ∧
              ∃ hmpos : 0 < S.m, ∀ W : ℝ, 0 < W → W ≤ (S.n : ℝ) ^ ω →
                let a := W / (S.K : ℝ)
                let β := fun _ : Site Λ ↦ Fin q
                let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
                  (FiniteProduct.splitEquiv β X) Ωt
                let d := E.card
                let n := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
                ∀ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
                  let pre : (k : ℕ) → Config k (fun v ↦ Fin (n v)) → ℂ := fun k ↦
                    replicaPrevector Ωt d k (ell k) ∘ augmentedSumReplicaCopiesEquiv q d k
                  let ψ : FiniteProduct.Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
                    compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
                  (∀ᶠ k : ℕ in atTop,
                    (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
                      ‖WithLp.toLp 2
                        (((1 : Matrix (Fin k → FiniteProduct.Configuration β Xᶜ)
                          (Fin k → FiniteProduct.Configuration β Xᶜ) ℂ) ⊗ₖ
                          labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
                          (fun x : (Fin k → FiniteProduct.Configuration β Xᶜ) ×
                            (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) →
                  ∃ c : ℝ, 0 ≤ c ∧
                    Tendsto (Real.bellOverlapRemainder d c S.K) atTop (𝓝 0) ∧
                    ∀ᶠ k : ℕ in atTop, ∀ (s : ℕ) (hs : s + 1 ≤ S.n * S.m) (p : ℝ),
                      let σ := terminalPartition S (S.n * S.m)
                      let gpost := fun j g ↦
                        regionalEntropy Λ q Ωt (positiveNear S.depth (σ j g)) +
                          regionalEntropy Λ q Ωt (positiveNearMiddle S.depth (σ j g)) -
                            regionalEntropy Λ q Ωt (middle (σ j g))
                      let p₀ := Set.projIcc (0 : ℝ) 1 zero_le_one p
                      let bound := fun (tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m))) ↦
                        2 * Real.log (d : ℝ) - Real.log z +
                          (a / 2) * (∑ g, ∑ j, tree.weight j * gpost j g) +
                            6 * (S.K : ℝ) * (C₀ * B) * a ^ 2 - (S.K : ℝ) / 2 * Real.log z +
                              Real.bellOverlapRemainder d c S.K k
                      let step : Fin (S.n * S.m) := ⟨s, Nat.lt_of_succ_le hs⟩
                      let Nfill := Matrix.Transport.filteredNormSq
                        ((S.actualFillData hmpos hM s).rootPath n (a / 2) k p) (pre k)
                      let Ncharge := Matrix.Transport.filteredNormSq
                        ((S.actualChargeData hmpos hM s).rootPath n (a / 2) k p) (pre k)
                      (0 < Nfill ∧ -Real.log Nfill / (k : ℝ) ≤
                        bound (((S.actualFillData hmpos hM s).tree p₀).map
                          (fillTerminalIndex S.K S.m S.M (S.n * S.m) step))) ∧
                      (0 < Ncharge ∧ -Real.log Ncharge / (k : ℝ) ≤
                        bound (((S.actualChargeData hmpos hM s).tree p₀).map
                          (chargeTerminalIndex S.K S.m S.M (S.n * S.m) step))) := by
  classical
  obtain ⟨Ctr, Ctarget, hCtr, hCtarget, Nt, hNt, htarget⟩ :=
    exists_truncated_target_typical_window hq R hJ hΔ hC_T
  obtain ⟨CB, hCB, hbudget⟩ := exists_statusMarginal_cutBudget_le_log hq R hCtr.le
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hc₀ : 0 < 1 / (32 * Real.sqrt
      (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J))) := by positivity
  refine ⟨Ctr, Ctarget, CB, hCtr, hCtarget, hCB, ?_⟩
  intro F ω hmargin
  obtain ⟨Na, _, hNa⟩ := F.exists_a_le_moment_radius (A := 6) hmargin hCB.le
    (by norm_num) (lt_min hc₀ zero_lt_one)
  obtain ⟨Ns, hNs⟩ := eventually_atTop.mp
    (eventually_status_scale_separation (ell := F.ell) hCtr.le
      F.kappa_pos F.kappa_lt_mu)
  refine ⟨max Nt (max Na Ns), hNt.trans (le_max_left _ _), ?_⟩
  intro Λ T _ hT h S hM E₀ Ω hgs hgraph hanchor hn hr hm hD hK hsize hdepth
    hrows hclear L X g ε w δ B C₀ c₀
  have hnT : Nt ≤ S.n := (le_max_left _ _).trans hn
  have hnA : Na ≤ S.n := (le_max_left Na Ns).trans ((le_max_right _ _).trans hn)
  have hnS : Ns ≤ S.n := (le_max_right Na Ns).trans ((le_max_right _ _).trans hn)
  have hmF : S.m = F.m S.n := hm
  have hDF : S.D = F.D S.n := hD
  have hKF : S.K = F.K S.n := by
    change S.K = F.L S.n / (8 * F.m S.n)
    rw [← hmF]
    exact hK
  have hscales := hNs S.n hnS
  change 2 ≤ S.n ∧ ⌈Ctr * Real.log (S.n : ℝ) ^ 2⌉₊ ≤ F.D S.n ∧
    1 ≤ F.D S.n ∧ 4 * F.D S.n ≤ F.m S.n ∧
      8 * F.K S.n * F.m S.n ≤ F.L S.n at hscales
  rw [← hmF, ← hDF, ← hKF, ← hr] at hscales
  obtain ⟨hn2, hrD, hDpos, hDm, hKL⟩ := hscales
  obtain ⟨hKpos, hsmall⟩ := hNa S.n hnA
  rw [← hKF] at hKpos
  have hmpos : 0 < S.m := by omega
  obtain ⟨hB, hcut⟩ := hbudget Λ T hT S hgraph hdepth hanchor L hn2 hr
    hrD hDpos hDm hKL hrows hclear
  obtain ⟨hcard, hX, hboundary, e, Ωt, htrgs, he0, he, hphase, htrace,
      hmoment, halltail, hBX, htail, hwindow⟩ :=
    htarget Λ h S E₀ Ω F T hT hgs hgraph hanchor hnT hr hsize hdepth hrows hclear
  refine ⟨hKpos, hB, by dsimp [C₀, g]; positivity, hc₀, hcard, hX, hboundary,
    e, Ωt, htrgs, he0, he, hphase, htrace, hmoment, halltail, hBX, htail, ?_⟩
  intro p E z
  refine ⟨hwindow, hmpos, ?_⟩
  intro W hW hWle a β ΩX d n ell pre ψ hmass
  have hBupper : B ≤ CB * (S.n : ℝ) * (F.D S.n : ℝ) *
      Real.log (S.n : ℝ) ^ 12 := by
    dsimp only [B]
    rw [← hDF]
    exact le_of_eq (by ring)
  have ha : 0 < a := div_pos hW (by exact_mod_cast (show 0 < S.K by omega))
  have hsmall' : 6 * a ≤ min c₀ 1 / Real.sqrt B := by
    simpa only [ScannerExponents.a, ← hKF] using
      hsmall W B hW.le hWle hB hBupper
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr (zero_lt_one.trans_le hB)
  have hsqrt1 : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hprod : 6 * a * Real.sqrt B ≤ min c₀ 1 := (le_div_iff₀ hsqrt).mp hsmall'
  have haRadius : 6 * a ≤ c₀ / Real.sqrt B :=
    (le_div_iff₀ hsqrt).mpr (hprod.trans (min_le_left _ _))
  have haOne : 6 * a ≤ 1 := calc
    6 * a ≤ 6 * a * Real.sqrt B := le_mul_of_one_le_right (by positivity) hsqrt1
    _ ≤ min c₀ 1 := hprod
    _ ≤ 1 := min_le_right _ _
  have hmom : ∀ (s : ℕ) (hist : History S.K S.m S.M s) (band : Fin S.K),
      (s ≤ S.n * S.m → ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
        ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
          Real.log (Entropy.surprisalMoment
            (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
            u * regionalEntropy Λ q Ωt Q + (C₀ * B) * u ^ 2) ∧
      (s + 1 ≤ S.n * S.m →
        ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
          ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
            Real.log (Entropy.surprisalMoment
              (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
              u * regionalEntropy Λ q Ωt Q + (C₀ * B) * u ^ 2) := by
    intro s hist band
    constructor
    · intro hs Q hQ u hu
      exact S.log_surprisalMoment_truncated_reducedState_le_common h Ω
        hgraph hanchor hΔ hgs.1 L htrgs Q ((hcut s hist band).1 hs Q hQ) hu
    · intro hs Q hQ u hu
      exact S.log_surprisalMoment_truncated_reducedState_le_common h Ω
        hgraph hanchor hΔ hgs.1 L htrgs Q ((hcut s hist band).2 hs Q hQ) hu
  have hρ : reducedState Λ q Ωt X =
      Matrix.partialTraceRight (Matrix.vecMulVec ΩX (star ΩX)) :=
    (reducedState_eq_finiteProduct Λ q Ωt X).trans
      (FiniteProduct.reducedPure_eq_partialTrace β Ωt X)
  have hzEq :
      (posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian.spectralRestrictionMass E =
        z := by simp only [← hρ]
  have hupper := eventually_actualScan_suppliedPrevector_sharp_upper hT S hdepth
    hmpos hM a (C₀ * B) (c₀ / Real.sqrt B) ha haRadius haOne L hKL Ωt htrgs.1
    E ell hmom (hzEq.symm ▸ hwindow.2.2.1) hmass
  simpa only [hzEq] using! hupper

end TNLean.PEPS.AreaLaw.Scan.CollarScan
