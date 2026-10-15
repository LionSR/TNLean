/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceActualInformation
import TNLean.PEPS.AreaLaw.Scan.FinalSharpErrorPower
import TNLean.PEPS.AreaLaw.Scan.FinalSharpTransportSmallness
import TNLean.PEPS.AreaLaw.Scan.PhysicalInformationDimension

/-!
# Conditional final-scale information for the concrete physical source

The same-source information theorem is composed with the uniform numerical
error absorption. The target dimension and truncated target entropy are
derived from the actual compact-volume and trace bounds. Literal rounded
scales put the final weight in the transport interval automatically.

The target and positive-prefix source entropy bounds, scanner construction,
layer bounds, scale separation, anchor multiplicity and geometric clearance
remain explicit antecedents. This theorem does not construct a scanner or
safe-box entropy input and does not claim Proposition 9.6 or the full area law.
See `docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 353--357, 399--533 and 839--941, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter ActualTerminals

open Classical in
/-- At the literal final scales, the same physical source has conditional
original-state collar information bounded by the exact maximal error power
and the paper's weaker sublinear power. The radius constant precedes the
source entropy coefficient; the information coefficient and size threshold
precede every physical instance. All original source geometry and entropy
hypotheses remain explicit. The fixed-instance replica limit is already
proved by the same-source information theorem and is not interchanged with
the size estimate. Source: `08-scanner.tex`, lines 868--941. -/
theorem exists_sourceTarget_finalScale_mutualInformation
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ)
    (hP : (Exponents.scannerNu : ℝ) ≤ P) :
    ∃ Ctr : ℝ, 0 < Ctr ∧
      ∀ Ce : ℝ, 0 ≤ Ce → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧
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
          let L := ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
              C * (S.n : ℝ) ^ (62497 / 62500 : ℝ) ∧
            2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
              C * (S.n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  classical
  obtain ⟨Ctr, Ctarget, CB, ct, Cent, eent, Cen, een, Cenergy, Cl,
      hCtr, hCtarget, hCB, hct, hCenergy, hCl, hsource⟩ :=
    exists_sourceTarget_actual_mutualInformation_bound hq R hJ hΔ hC_T
      hC₁ multiplicity hmultiplicity P hP
  let g := Δ / positiveNormalization 1 (Δ / 2) J
  let C₀ := 512 * Real.exp 1 * (2 / g)
  have hg : 0 < g := div_pos hΔ (positiveNormalization_pos 1 (Δ / 2) J)
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hCvol : 0 ≤ C_T + 1 := by linarith
  obtain ⟨Nt, htarget⟩ := eventually_atTop.mp
    (eventually_abs_regionalEntropy_sub_le_of_truncation q hq g (C_T + 1) hg)
  obtain ⟨Nsml, hNsml, hsmall⟩ := exists_finalSharp_transport_smallness hq hCtr.le hct
  refine ⟨Ctr, hCtr, ?_⟩
  intro Ce hCe
  obtain ⟨Ns, hNs, hsourceN⟩ := hsource Ce hCe
  obtain ⟨C, hC, Ne, hNe, herror⟩ := exists_finalSharp_source_error_le
    q hq Ce C₀ CB g (C_T + 1) hCe hC₀ hCB.le hg hCvol
  refine ⟨C, hC, max Ns (max Ne (max Nt Nsml)), hNs.trans (le_max_left _ _), ?_⟩
  intro Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix hrD hDpos hDm L X β
  have hnS : Ns ≤ S.n := by omega
  have hnE : Ne ≤ S.n := by omega
  have hnT : Nt ≤ S.n := by omega
  have hnSmall : Nsml ≤ S.n := by omega
  have hn2 : 2 ≤ S.n := hNs.trans hnS
  have hn1 : (1 : ℝ) ≤ S.n := by exact_mod_cast (show 1 ≤ S.n by omega)
  let W := (S.n : ℝ) ^ (Exponents.scannerOmega : ℝ)
  let a := W / (S.K : ℝ)
  let τ := (S.n : ℝ) ^ (-(1 / 4000 : ℝ))
  let B := CB * ((S.n : ℝ) * S.D * Real.log (S.n : ℝ) ^ 12)
  let Bsh := Ce * ((S.n : ℝ) * (L : ℝ) ^ (Exponents.boxError : ℝ) + S.n) +
    (S.n : ℝ) ^ (-247 : ℝ)
  obtain ⟨hm, hM, hdata⟩ := hsourceN Λ T hT h S E₀ Ω hgs hgraph hanchor hnS
    hr hmScale hDScale hKScale hCeq hsize hdepth hrows hmult hclear
    htargetEntropy hprefix hrD hDpos hDm
  obtain ⟨hK, hKL, hB, hcard, hX, e, Ωt, htrgs, he0, he, htrace, hBX, htail, hwdata⟩ :=
    hdata
  let w := (S.n : ℝ) ^ ((3 : ℝ) / 5)
  let E := Entropy.typicalSet (reducedState_isHermitian Λ q Ωt X).eigenvalues
    (regionalEntropy Λ q Ωt X) w
  let z := (reducedState_isHermitian Λ q Ωt X).spectralRestrictionMass E
  obtain ⟨hwindow, hd, hpdata⟩ := hwdata
  let : NeZero E.card := NeZero.of_pos hd
  let St := regionalEntropy Λ q Ωt X
  let c := w - Real.log z
  let Bpre := 2 * St + 2 * Bsh + 6 * (S.n : ℝ) * (S.D : ℝ) * Real.log q
  let t := Matrix.traceDistance (Matrix.vecMulVec Ωt.ofLp (star Ωt.ofLp))
    (Matrix.vecMulVec Ω.ofLp (star Ω.ofLp))
  let dlog := Real.log (Real.exp 1 * Fintype.card (FiniteProduct.Configuration β X))
  let continuity := 16 * Real.sqrt t * dlog
  obtain ⟨ell, hpre, hdim, hinfo⟩ := hpdata
  have hΩt : ‖Ωt‖ = 1 := (Matrix.isGappedGroundState_iff.mp htrgs).1
  have hXcard : (X.card : ℝ) ≤ (C_T + 1) * (S.n : ℝ) ^ 2 :=
    (Nat.cast_le.mpr (Finset.card_le_card hX)).trans hcard
  have htargetCont := htarget S.n hnT Λ Ω Ωt hgs.1 hΩt X hXcard htrace
  have hSt : St ≤ Ce * (S.n : ℝ) ^ (1 + (Exponents.boxError : ℝ)) +
      (S.n : ℝ) ^ (-247 : ℝ) := by
    have h := le_abs_self (regionalEntropy Λ q Ωt X - regionalEntropy Λ q Ω X)
    dsimp only [St]
    linarith
  have hdlog : dlog ≤ 1 + ((C_T + 1) * Real.log q) * (S.n : ℝ) ^ 2 :=
    log_exp_configuration_card_le_of_card hq X hXcard
  have herrorN := herror S.n hnE
  simp only [← hmScale, ← hKScale] at herrorN
  obtain ⟨_, ha, hτ, hτhalf, hbound⟩ := herrorN
  have hsmallN := (hsmall S.n hnSmall).2.2
  simp only [← hmScale, ← hKScale, roundedLogRadius, ← hr] at hsmallN
  have hW : 1 ≤ W := Real.one_le_rpow hn1 (by norm_num [Exponents.scannerOmega])
  have hMI := hinfo W hW le_rfl hsmallN τ hτ hτhalf
  change 2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
    sharpInformationBound St c Bpre (Real.log z) W τ
      ((S.n : ℝ) ^ (-(1 / 2000 : ℝ)))
      ((3 + 1 / a) * Real.binEntropy τ + 37 * (C₀ * B) * a - Real.log z / a)
      continuity at hMI
  have herrorEq : finalSharpError S.n a C₀ B St Bsh z (Real.log q) t dlog =
      sharpInformationBound St c Bpre (Real.log z) W τ
        ((S.n : ℝ) ^ (-(1 / 2000 : ℝ)))
        ((3 + 1 / a) * Real.binEntropy τ + 37 * (C₀ * B) * a - Real.log z / a)
        continuity := by
    dsimp only [finalSharpError, sharpInformationBound, W, τ, c, Bpre, continuity, w]
    rw [hDScale]
    ring
  rw [← herrorEq] at hMI
  have hbudget : B ≤ CB * ((S.n : ℝ) *
      (Nat.ceil ((S.n : ℝ) ^ (Exponents.scannerKappa : ℝ)) : ℝ) *
        Real.log (S.n : ℝ) ^ 12) := by simp only [B, hDScale, le_refl]
  have hscalar := hbound B St Bsh z t dlog hwindow.2.2.1 hwindow.2.2.2.1
    hwindow.2.1 hSt le_rfl hbudget htrace hdlog
  exact ⟨hMI.trans hscalar.1, hMI.trans hscalar.2⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
