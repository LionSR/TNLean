/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.TargetTypicalWindow
import TNLean.PEPS.AreaLaw.Scan.StatusMarginalMoments
import TNLean.PEPS.AreaLaw.Scan.StatusScaleSeparation
import TNLean.PEPS.AreaLaw.Scan.SharpMomentScale

/-!
# One target window for both sharp marginal-moment conditions

One quantitative truncated ground vector supplies the target typical set,
its physical spectral mass and all five status marginal moments. The literal
rounded scanner scales and an explicit positive exponent margin place ten
times the per-band weight in the common moment interval and below one. The
factor-six upper conditions follow from these same bounds.

The truncation, target-budget and status-budget constants precede the scanner
exponents and every physical instance. The threshold can depend on the fixed
exponent margin. The physical witness is selected before the weight and before
any label sequence, so both sharp consumers may use the same supplied sequence.
No sharp comparison, selected-charge defect estimate or absorption is asserted.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 70–85, 383–418 and 550–651;
`08-scanner.tex`, lines 32–58, 400–474 and 859–865, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter

/-- The explicit threshold of the sharp marginal-moment window: the target-window threshold,
the moment-radius threshold at multiple `10` and radius `min c₀ 1` with
`c₀ = 1 / (32 √(1 + 2 / g))`, and the status-scale separation threshold
(`08-scanner.tex`, lines 32–58, 400–474 and 859–865). -/
noncomputable def targetSharpMomentThreshold (q R : ℕ) (Ctr g : ℝ) (F : ScannerExponents)
    (ω : ℝ) : ℕ :=
  max (targetTypicalWindowThreshold q R Ctr g)
    (max (F.momentRadiusThreshold ω (statusMarginalBudgetConstant q R Ctr) 10
      (min (1 / (32 * Real.sqrt (1 + 2 / g))) 1))
      (statusScaleSeparationThreshold Ctr F.kappa F.mu))

open Classical in
/-- One source target-window witness has common status moments and both sharp smallness
conditions at every `S.n` from the explicit threshold `targetSharpMomentThreshold` on, with the
explicit target and status budget coefficients `targetBudgetConstant q R Ctr` and
`statusMarginalBudgetConstant q R Ctr`. Source: `07-comparators.tex`, lines 70–85, 383–418
and 550–651; `08-scanner.tex`, lines 32–58, 400–474 and 859–865. -/
theorem exists_truncated_target_sharp_moments_of_targetSharpMomentThreshold_le {q : ℕ}
    [NeZero q]
    (hq : 1 ≤ q) (R : ℕ) {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ (F : ScannerExponents) (ω : ℝ),
        ω + (1 + F.kappa) / 2 < 1 - F.ell - F.mu →
          ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
            (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
            (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
            (E₀ : ℝ) (Ω : StateSpace Λ q),
            IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
            targetSharpMomentThreshold q R Ctr (Δ / positiveNormalization 1 (Δ / 2) J) F ω ≤
              S.n →
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
            let B := statusMarginalBudgetConstant q R Ctr *
              ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
            let C₀ := 512 * Real.exp 1 * (2 / g)
            let c₀ := 1 / (32 * Real.sqrt (1 + 2 / g))
            1 ≤ S.K ∧ 0 < S.m ∧ 8 * S.K * S.m ≤ L ∧
            1 ≤ B ∧ 0 < C₀ ∧ 0 < c₀ ∧
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
                targetBudgetConstant q R Ctr * (S.n : ℝ) * Real.log (S.n : ℝ) ^ 12 ∧
              Entropy.surprisalTail (reducedState_isHermitian Λ q Ωt X).eigenvalues
                (regionalEntropy Λ q Ωt X) w ≤ δ ∧
              let p := (reducedState_isHermitian Λ q Ωt X).eigenvalues
              let E := Entropy.typicalSet p (regionalEntropy Λ q Ωt X) w
              let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
              (0 < 1 - δ ∧ 1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧ E.Nonempty ∧
                ∀ i ∈ E, 0 < p i ∧
                  Real.exp (-regionalEntropy Λ q Ωt X - w) ≤ p i ∧
                  p i ≤ Real.exp (-regionalEntropy Λ q Ωt X + w)) ∧
              (∀ (s : ℕ) (hist : History S.K S.m S.M s) (band : Fin S.K),
                (s ≤ S.n * S.m →
                  ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
                    ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                      Real.log (Entropy.surprisalMoment
                        (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                        u * regionalEntropy Λ q Ωt Q + (C₀ * B) * u ^ 2) ∧
                (s + 1 ≤ S.n * S.m →
                  ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                    ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                      Real.log (Entropy.surprisalMoment
                        (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                        u * regionalEntropy Λ q Ωt Q + (C₀ * B) * u ^ 2)) ∧
              ∀ W : ℝ, 0 < W → W ≤ (S.n : ℝ) ^ ω →
                let a := W / (S.K : ℝ)
                0 < a ∧ 10 * a ≤ c₀ / Real.sqrt B ∧ 10 * a ≤ 1 ∧
                  6 * a ≤ c₀ / Real.sqrt B ∧ 6 * a ≤ 1 := by
  classical
  obtain ⟨Ctr, hCtr, hwindow⟩ :=
    exists_truncated_target_typical_window_of_targetTypicalWindowThreshold_le R hJ hΔ hC_T
  have htarget := hwindow q hq
  have hbudget := statusMarginal_cutBudget_le_log hq R hCtr.le
  set CB := statusMarginalBudgetConstant q R Ctr
  have hCB : 0 < CB := statusMarginalBudgetConstant_pos q R hCtr.le
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hc₀ : 0 < 1 / (32 * Real.sqrt
      (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J))) := by positivity
  refine ⟨Ctr, hCtr, ?_⟩
  intro F ω hmargin
  let Nt := targetTypicalWindowThreshold q R Ctr (Δ / positiveNormalization 1 (Δ / 2) J)
  let Na := F.momentRadiusThreshold ω CB 10
    (min (1 / (32 * Real.sqrt (1 + 2 / (Δ / positiveNormalization 1 (Δ / 2) J)))) 1)
  have hNa := fun n (hn : Na ≤ n) => F.a_le_moment_radius_of_momentRadiusThreshold_le
    (A := 10) hmargin hCB.le (by norm_num) (lt_min hc₀ zero_lt_one) hn
  let Ns := statusScaleSeparationThreshold Ctr F.kappa F.mu
  have hNs := fun n (hn : Ns ≤ n) => status_scale_separation_of_threshold_le
    (ell := F.ell) hCtr.le F.kappa_pos F.kappa_lt_mu hn
  intro Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hm hD hK hsize hdepth
    hrows hclear L X g ε w δ B C₀ c₀
  replace hn : max Nt (max Na Ns) ≤ S.n := hn
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
  refine ⟨hKpos, hmpos, hKL, hB, by dsimp [C₀, g]; positivity, hc₀,
    hcard, hX, hboundary, e, Ωt, htrgs, he0, he, hphase, htrace,
    hmoment, halltail, hBX, htail, ?_⟩
  intro p E z
  refine ⟨hwindow, ?_, ?_⟩
  · intro s hist band
    constructor
    · intro hs Q hQ u hu
      exact S.log_surprisalMoment_truncated_reducedState_le_common h Ω
        hgraph hanchor hΔ hgs.1 L htrgs Q ((hcut s hist band).1 hs Q hQ) hu
    · intro hs Q hQ u hu
      exact S.log_surprisalMoment_truncated_reducedState_le_common h Ω
        hgraph hanchor hΔ hgs.1 L htrgs Q ((hcut s hist band).2 hs Q hQ) hu
  · intro W hW hWle a
    have hBupper : B ≤ CB * (S.n : ℝ) * (F.D S.n : ℝ) *
        Real.log (S.n : ℝ) ^ 12 := by
      dsimp only [B]
      rw [← hDF]
      exact le_of_eq (by ring)
    have ha : 0 < a := div_pos hW (by exact_mod_cast (show 0 < S.K by omega))
    have hsmall' : 10 * a ≤ min c₀ 1 / Real.sqrt B := by
      simpa only [ScannerExponents.a, ← hKF] using
        hsmall W B hW.le hWle hB hBupper
    have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr (zero_lt_one.trans_le hB)
    have hsqrt1 : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
    have hprod : 10 * a * Real.sqrt B ≤ min c₀ 1 := (le_div_iff₀ hsqrt).mp hsmall'
    have haRadius : 10 * a ≤ c₀ / Real.sqrt B :=
      (le_div_iff₀ hsqrt).mpr (hprod.trans (min_le_left _ _))
    have haOne : 10 * a ≤ 1 := calc
      10 * a ≤ 10 * a * Real.sqrt B :=
        le_mul_of_one_le_right (by positivity) hsqrt1
      _ ≤ min c₀ 1 := hprod
      _ ≤ 1 := min_le_right _ _
    have hle : 6 * a ≤ 10 * a := by linarith
    exact ⟨ha, haRadius, haOne, hle.trans haRadius, hle.trans haOne⟩

open Classical in
/-- One source target-window witness has common status moments and both sharp
smallness conditions, uniformly over every admissible positive total weight.
The band count retains natural-number division, the history and collar lengths
retain their floors, and the separation retains its ceiling. The positive
exponent margin is explicit; it is not implied by ordinary scanner exponents.

Source: `07-comparators.tex`, lines 70–85, 383–418 and 550–651;
`08-scanner.tex`, lines 32–58, 400–474 and 859–865. -/
theorem exists_truncated_target_sharp_moments {q : ℕ} [NeZero q]
    (hq : 1 ≤ q) (R : ℕ) {J Δ C_T : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) :
    ∃ Ctr Ctarget CB : ℝ, 0 < Ctr ∧ 0 < Ctarget ∧ 0 < CB ∧
      ∀ (F : ScannerExponents) (ω : ℝ),
        ω + (1 + F.kappa) / 2 < 1 - F.ell - F.mu →
        ∃ N : ℕ, 2 ≤ N ∧
          ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
            (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
            (S : CollarScan (Site Λ) (AdmissibleSupport Λ R))
            (E₀ : ℝ) (Ω : StateSpace Λ q),
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
            1 ≤ S.K ∧ 0 < S.m ∧ 8 * S.K * S.m ≤ L ∧
            1 ≤ B ∧ 0 < C₀ ∧ 0 < c₀ ∧
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
              (∀ (s : ℕ) (hist : History S.K S.m S.M s) (band : Fin S.K),
                (s ≤ S.n * S.m →
                  ∀ Q ∈ statusMarginalRegions S.depth (S.state hist band),
                    ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                      Real.log (Entropy.surprisalMoment
                        (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                        u * regionalEntropy Λ q Ωt Q + (C₀ * B) * u ^ 2) ∧
                (s + 1 ≤ S.n * S.m →
                  ∀ Q ∈ statusMarginalRegions S.depth (S.oldChargeState hist band),
                    ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
                      Real.log (Entropy.surprisalMoment
                        (reducedState_isHermitian Λ q Ωt Q).eigenvalues u) ≤
                        u * regionalEntropy Λ q Ωt Q + (C₀ * B) * u ^ 2)) ∧
              ∀ W : ℝ, 0 < W → W ≤ (S.n : ℝ) ^ ω →
                let a := W / (S.K : ℝ)
                0 < a ∧ 10 * a ≤ c₀ / Real.sqrt B ∧ 10 * a ≤ 1 ∧
                  6 * a ≤ c₀ / Real.sqrt B ∧ 6 * a ≤ 1 := by
  obtain ⟨Ctr, hCtr, hall⟩ :=
    exists_truncated_target_sharp_moments_of_targetSharpMomentThreshold_le hq R hJ hΔ hC_T
  exact ⟨Ctr, _, _, hCtr, one_pos.trans_le (le_max_left _ _),
    statusMarginalBudgetConstant_pos q R hCtr.le, fun F ω hmargin =>
      ⟨_, (le_max_left _ _).trans (le_max_left _ _), hall F ω hmargin⟩⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
