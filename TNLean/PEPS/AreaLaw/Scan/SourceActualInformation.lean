/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceSelectedSharpEnergy
import TNLean.PEPS.AreaLaw.Scan.ActualSelectedCollarInformation
import TNLean.PEPS.AreaLaw.Scan.SourceActualTerminalEntropy
import TNLean.PEPS.AreaLaw.Scan.SharpInformationScalar

/-!
# Physical information from the same source-selected sharp comparison

The concrete strong-density/energy consumer is invoked once. Its unchanged
truncated vector, spectral window and physical label sequence supply the
actual terminal entropy estimates and information identity. At each replica
count its very same selected charge point supplies the sharp inequality.
The terminal entropy terms are eliminated, and only then are the replica
remainders sent to zero at fixed physical data, weight and smoothing parameter.

The original target and positive-prefix entropy hypotheses, scanner geometry
and transport smallness remain explicit. No safe-box entropy conclusion or
final size-power estimate is assumed or claimed. See
`docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 353--357, 399--533 and 839--941, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter ActualTerminals
open Classical in
/-- The actual physical collar information obeys the scalar sharp bound using one source witness
and label sequence, at every `S.n` from the explicit threshold
`sourceSelectedSharpEnergyThreshold` on, with the budget coefficients
`targetBudgetConstant q R Ctr` and `statusMarginalBudgetConstant q R Ctr`. The truncation
constant `Ctr` and the transport constants `ct, Cent, eent, Cen, een` remain existential.
Source: `08-scanner.tex`, lines 868--911 and 936--941. -/
theorem exists_sourceTarget_actual_mutualInformation_bound_of_threshold_le
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ)
    (hP : (Exponents.scannerNu : ℝ) ≤ P) :
    ∃ Ctr ct Cent eent Cen een : ℝ, 0 < Ctr ∧ 0 < ct ∧
      ∀ Ce : ℝ, 0 ≤ Ce →
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
          (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
          (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
          sourceSelectedSharpEnergyThreshold q R (Δ / positiveNormalization 1 (Δ / 2) J) C_T C₁
            multiplicity P Ce Ctr Cent eent Cen een ≤ S.n →
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
          let B := statusMarginalBudgetConstant q R Ctr *
            ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
          let C₀ := 512 * Real.exp 1 * (2 / g)
          let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + S.n) +
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
            let _dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
            let _energy := S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)
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
            let _gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
            let tree := fun (s : Fin (S.n * S.m)) (p : ℝ) ↦
              ((S.actualChargeData hm hM s.val).tree
                (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
                (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
            let _Gpre := fun s p ↦
              (∑ band, ∑ j, (tree s p).weight j * gpre j band) / (S.K : ℝ)
            let _Gpost := fun s p ↦
              (∑ band, ∑ j, (tree s p).weight j * gpost j band) / (S.K : ℝ)
            let St := regionalEntropy Λ q Ωt X
            let c := w - Real.log z
            let Bpre := 2 * St + 2 * Bsh +
              6 * (S.n : ℝ) * (S.D : ℝ) * Real.log q
            let continuity := 16 * Real.sqrt (Matrix.traceDistance
              (Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))
              (Matrix.vecMulVec Ω.ofLp (star Ω.ofLp))) *
                Real.log (Real.exp 1 * Fintype.card (FiniteProduct.Configuration β X))
            ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
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
                ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                  2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
                    sharpInformationBound St c Bpre (Real.log z) W τ
                      ((S.n : ℝ) ^ (-(1 / 2000 : ℝ)))
                      ((3 + 1 / a) * Real.binEntropy τ + 37 * (C₀ * B) * a -
                        Real.log z / a) continuity := by
  classical
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, hsource⟩ :=
    exists_sourceTarget_selected_actualCharge_sharp_energy_of_threshold_le hq R hJ hΔ hC_T
      hC₁ multiplicity hmultiplicity P hP
  have hg : 0 < Δ / positiveNormalization 1 (Δ / 2) J :=
    div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hterminal := fun n (hn : truncationEntropyThreshold q
      (Δ / positiveNormalization 1 (Δ / 2) J) (C_T + 1) ≤ n) =>
    source_actualTerminal_preEntropy_bounds_of_truncationEntropyThreshold_le q hq _ (C_T + 1) hg hn
  refine ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, ?_⟩
  intro Ce hCe Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix hrD hDpos hDm
  have hnT := hn
  simp only [sourceSelectedSharpEnergyThreshold, max_le_iff] at hnT
  replace hnT := hnT.2.2.2.1
  have hnpos : 0 < S.n := lt_of_lt_of_le two_pos
    ((two_le_sourceSelectedSharpEnergyThreshold _ _ _ _ _ _ _ _ _ _ _ _ _).trans hn)
  obtain ⟨hm, hM, hdata⟩ := hsource Ce hCe Λ T hT h S E₀ Ω hgs hgraph hanchor hn
    hr hmScale hDScale hKScale hCeq hsize hdepth hrows hmult hclear
    htargetEntropy hprefix hrD hDpos hDm
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
    St c Bpre continuity
  have hΩt : ‖Ωt‖ = 1 := (Matrix.isGappedGroundState_iff.mp htrgs).1
  have hKpos : 0 < S.K := by omega
  have hSt : 0 ≤ St := regionalEntropy_nonneg Λ q Ωt hΩt X
  have hselected := abs_log_card_and_selectedSchmidtEntropy_sub_le
    Ωt hΩt X E w hwindow.2.2.1 (fun i hi ↦ (hwindow.2.2.2.2.2 i hi).2)
  change |Real.log (d : ℝ) - St| ≤ c ∧ |Sent - St| ≤ c at hselected
  have hc : 0 ≤ c := (abs_nonneg _).trans hselected.1
  have hlogd : Real.log (d : ℝ) ≤ St + c := by
    linarith only [(abs_le.mp hselected.1).2]
  have hSent : Sent ≤ St + c := by linarith only [(abs_le.mp hselected.2).2]
  have hpreBounds := hterminal S.n hnT (AdmissibleSupport Λ R) Λ T hT S
    rfl hgraph hdepth hnpos hKpos (by omega) hDpos hDm L hKL hrows
    Ω Ωt hgs.1 hΩt hcard htrace Ce (Exponents.boxError : ℝ) hprefix
  change 0 ≤ gmax ∧ gmax ≤ max 0 Bpre ∧
    ∀ tree : MeanTree (terminalFamily S.K S.m S.M (S.n * S.m)),
      0 ≤ (∑ band, ∑ j, tree.weight j * gpre j band) / (S.K : ℝ) ∧
        (∑ band, ∑ j, tree.weight j * gpre j band) / (S.K : ℝ) ≤ Bpre at hpreBounds
  have hBsh : 0 ≤ Bsh := by dsimp only [Bsh]; positivity
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hBpre : 0 ≤ Bpre := by dsimp only [Bpre]; positivity
  have hgmax : gmax ≤ Bpre := by
    simpa only [max_eq_right hBpre] using hpreBounds.2.1
  obtain ⟨ell, hpre, hdim, hweights⟩ := hpdata
  refine ⟨ell, hpre, hdim, ?_⟩
  intro W hW hWupper a ℓ hasmall τ hτ hτhalf
  have hWpos : 0 < W := zero_lt_one.trans_le hW
  obtain ⟨b, rem, Cb, cU, cL, Cf, cR, Ci,
      hCb, hcU, hcL, hCf, hcR, hCi, hb0, hb, hrem0, hrem, hlimU, hlimL,
      hlimR, hpoints⟩ := hweights W hW hWupper hasmall
  apply information_le_of_eventually_sharpInformationBound (g := g) hrem hlimU hlimL
  filter_upwards [hpoints] with k hk
  obtain ⟨s, p, hp, hQ0, hQ, hδ0, hδcap, hδpower, hsharp⟩ := hk
  have hMI := (actualCharge_two_mutualInformation_le_selectedSharpExpression hT S hdepth
    hm hM hKpos L hKL Ωt hΩt E w hwindow.2.2.1
    (fun i hi ↦ (hwindow.2.2.2.2.2 i hi).2) s p).2 Ω hgs.1
  have hGpre : Gpre s p ≤ Bpre := (hpreBounds.2.2 (tree s p)).2
  have hδ : 0 ≤ (S.n : ℝ) ^ (-(1 / 2000 : ℝ)) + rem k / (g / 2) :=
    add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg S.n) _)
      (div_nonneg (hrem0 k) (le_of_lt (div_pos hg (by norm_num))))
  have hsharpτ := hsharp τ hτ hτhalf
  change 2 * Sent + Gpre s p - Gpost s p ≤
    2 * (2 * Real.log (d : ℝ) - Real.log z) / W +
      τ * Gpre s p + 2 * τ * Real.log (d : ℝ) +
      (3 + 1 / a) * Real.binEntropy τ + 37 * (C₀ * B) * a -
      Real.log z / a +
      ((S.n : ℝ) ^ (-(1 / 2000 : ℝ)) + rem k / (g / 2)) / τ *
        max 0 (2 * Sent + gmax) +
      2 * Real.bellOverlapRemainder d cU S.K k / W +
      sharpLowerRemainder a cL Cf ell Sent k at hsharpτ
  apply two_information_le_sharpInformationBound
    hWpos hτ hδ hSt hc hBpre hlogd hSent hGpre hgmax
  · simpa only [add_assoc, sub_eq_add_neg] using hsharpτ
  · exact hMI

open Classical in
/-- The actual physical collar information obeys the scalar sharp bound
using one source witness and label sequence. Fixed physical constants
precede the source entropy coefficient, which precedes the size threshold.
The label sequence precedes the weight; the replica limit is taken only
after fixing that weight and the positive smoothing parameter. The original
source geometry and entropy inputs remain explicit.
Source: `08-scanner.tex`, lines 868--911 and 936--941. -/
theorem exists_sourceTarget_actual_mutualInformation_bound
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ)
    (hP : (Exponents.scannerNu : ℝ) ≤ P) :
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
          let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + S.n) +
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
            let _dims := augmentedDimensions (V := Site Λ) q (fun _ ↦ d)
            let _energy := S.actualEnergyTerms h Ω Δ L (fun _ ↦ d)
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
            let _gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
            let tree := fun (s : Fin (S.n * S.m)) (p : ℝ) ↦
              ((S.actualChargeData hm hM s.val).tree
                (Set.projIcc (0 : ℝ) 1 zero_le_one p)).map
                (chargeTerminalIndex S.K S.m S.M (S.n * S.m) s)
            let _Gpre := fun s p ↦
              (∑ band, ∑ j, (tree s p).weight j * gpre j band) / (S.K : ℝ)
            let _Gpost := fun s p ↦
              (∑ band, ∑ j, (tree s p).weight j * gpost j band) / (S.K : ℝ)
            let St := regionalEntropy Λ q Ωt X
            let c := w - Real.log z
            let Bpre := 2 * St + 2 * Bsh +
              6 * (S.n : ℝ) * (S.D : ℝ) * Real.log q
            let continuity := 16 * Real.sqrt (Matrix.traceDistance
              (Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))
              (Matrix.vecMulVec Ω.ofLp (star Ω.ofLp))) *
                Real.log (Real.exp 1 * Fintype.card (FiniteProduct.Configuration β X))
            ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
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
                ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
                  2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
                    sharpInformationBound St c Bpre (Real.log z) W τ
                      ((S.n : ℝ) ^ (-(1 / 2000 : ℝ)))
                      ((3 + 1 / a) * Real.binEntropy τ + 37 * (C₀ * B) * a -
                        Real.log z / a) continuity := by
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, hct, hall⟩ :=
    exists_sourceTarget_actual_mutualInformation_bound_of_threshold_le hq R hJ hΔ hC_T hC₁
      multiplicity hmultiplicity P hP
  have hcoeff := transport_coefficients_log_bound (NeZero.pos q) hCtr.le
    (10 * (10 * (multiplicity : ℝ)) ^ (7 / 8 : ℝ) * |Cen|) een
    (50 * (multiplicity : ℝ) * (2 : ℝ) ^ (1 / 8 : ℝ) * |Cen|) (een + 1 / 8)
  exact ⟨Ctr, _, _, ct, Cent, eent, Cen, een,
    actualChargeEnergyCoefficient q Ctr multiplicity Cen een, _, hCtr,
    one_pos.trans_le (le_max_left _ _), statusMarginalBudgetConstant_pos q R hCtr.le, hct,
    one_le_mul_of_one_le_of_one_le (by norm_num) hcoeff.1, hcoeff.2.1,
    fun Ce hCe => ⟨_, two_le_sourceSelectedSharpEnergyThreshold _ _ _ _ _ _ _ _ _ _ _ _ _,
      hall Ce hCe⟩⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
