/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.SourceFinalInformation
import TNLean.PEPS.AreaLaw.Scan.FinalScannerAdmissibility

/-!
# Final physical information from the literal rounded scales

The final conditional source theorem no longer needs separate numerical
scale-separation hypotheses. The literal floor and ceiling definitions
supply them after increasing a single uniform physical-size threshold.

The physical scanner, template and target/prefix entropy hypotheses remain
explicit. This result does not construct the safe-box entropy input and
is not the unconditional collar theorem or the full area law.
See `docs/paper-gaps/arealaw2d_safe_box_collar_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 32--58 and 808--941, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text reused.
-/

noncomputable section

open Matrix TensorPower TensorPower.ReplicaTransport PermutationRepresentation Filter
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

open SpectralFilter ActualTerminals

/-- The explicit threshold of the final-scale source information at the literal rounded
scales: the final-scale source information threshold and the final scanner admissibility
threshold (`08-scanner.tex`, lines 32--58 and 808--941). -/
noncomputable def sourceRoundedInformationThreshold (q R : ℕ) (g C_T C₁ : ℝ)
    (multiplicity : ℕ) (P Ce Ctr ct Cent eent Cen een : ℝ) : ℕ :=
  max (sourceFinalInformationThreshold q R g C_T C₁ multiplicity P Ce Ctr ct Cent eent Cen een)
    (finalScannerAdmissibilityThreshold Ctr)

/-- The rounded-scale source information threshold is at least two. -/
theorem two_le_sourceRoundedInformationThreshold (q R : ℕ) (g C_T C₁ : ℝ)
    (multiplicity : ℕ) (P Ce Ctr ct Cent eent Cen een : ℝ) :
    2 ≤ sourceRoundedInformationThreshold q R g C_T C₁ multiplicity P Ce Ctr ct Cent eent Cen
      een :=
  (two_le_sourceFinalInformationThreshold _ _ _ _ _ _ _ _ _ _ _ _ _ _).trans (le_max_left _ _)

open Classical in
/-- The rounded-scale collar information bound of
`exists_sourceTarget_finalScale_mutualInformation_of_rounded_scales_of_threshold_le` at the named
truncation constant `Ctr = latticeTruncationRadiusConstant R J Δ (C_T + 1)`, which depends only
on `R, J, Δ, C_T`, and at any transport constants with `0 < ct` satisfying the finite-family
transport bound. Source: `08-scanner.tex`, lines 32--58 and 808--941. -/
theorem sourceTarget_finalScale_mutualInformation_of_rounded_scales_explicit
    {q : ℕ} [NeZero q] (hq : 1 ≤ q) (R : ℕ)
    {J Δ C_T C₁ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hC_T : 0 ≤ C_T) (hC₁ : 0 < C₁) (multiplicity : ℕ)
    (hmultiplicity : 3 * (multiplicity : ℝ) ≤ C₁) (P : ℝ)
    (hP : (Exponents.scannerNu : ℝ) ≤ P)
    {ct Cent eent Cen een : ℝ} (hct : 0 < ct)
    (htransport : FiniteFamilyTransportBound ct Cent eent Cen een)
    {Ctr : ℝ} (hCtrEq : Ctr = latticeTruncationRadiusConstant R J Δ (C_T + 1)) :
      ∀ Ce : ℝ, 0 ≤ Ce →
        ∀ (Λ T : Finset (ℤ × ℤ)) [LinearOrder (AdmissibleSupport Λ R)]
          (hT : T.Nonempty) (h : LocalHamiltonian Λ q R J)
          (S : CollarScan (Site Λ) (AdmissibleSupport Λ R)) (E₀ : ℝ)
          (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          S.graph = domainGraph Λ → (∀ i, S.anchor i ∈ i.val) →
          sourceRoundedInformationThreshold q R (Δ / positiveNormalization 1 (Δ / 2) J) C_T C₁
            multiplicity P Ce Ctr ct Cent eent Cen een ≤ S.n →
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
          let L := ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
              sourceFinalInformationConstant q (Δ / positiveNormalization 1 (Δ / 2) J) C_T Ce *
                (S.n : ℝ) ^ (62497 / 62500 : ℝ) ∧
            2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
              sourceFinalInformationConstant q (Δ / positiveNormalization 1 (Δ / 2) J) C_T Ce *
                (S.n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  classical
  have hsource := sourceTarget_finalScale_mutualInformation_explicit hq R hJ hΔ hC_T hC₁
    multiplicity hmultiplicity P hP hct htransport hCtrEq
  have hCtr : 0 < Ctr := by
    rw [hCtrEq]; exact latticeTruncationRadiusConstant_pos R hΔ (by positivity)
  intro Ce hCe Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix
  have hscales := finalScanner_admissibility_of_threshold_le hCtr.le
    ((le_max_right _ _).trans hn)
  simp only [roundedLogRadius, ← hmScale, ← hDScale, ← hKScale, ← hr] at hscales
  exact hsource Ce hCe Λ T hT h S E₀ Ω hgs hgraph hanchor ((le_max_left _ _).trans hn) hr
    hmScale hDScale hKScale hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix
    hscales.1 hscales.2.1 hscales.2.2.1

open Classical in
/-- The concrete original-state information bound at the literal rounded final scales, with the
explicit coefficient `sourceFinalInformationConstant` at every `S.n` from the explicit threshold
`sourceRoundedInformationThreshold` on. The truncation constant `Ctr` and the transport
constants `ct, Cent, eent, Cen, een` remain existential. All geometric and entropy premises are
retained. Source: `08-scanner.tex`, lines 32--58 and 808--941. -/
theorem exists_sourceTarget_finalScale_mutualInformation_of_rounded_scales_of_threshold_le
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
          sourceRoundedInformationThreshold q R (Δ / positiveNormalization 1 (Δ / 2) J) C_T C₁
            multiplicity P Ce Ctr ct Cent eent Cen een ≤ S.n →
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
          let L := ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
              sourceFinalInformationConstant q (Δ / positiveNormalization 1 (Δ / 2) J) C_T Ce *
                (S.n : ℝ) ^ (62497 / 62500 : ℝ) ∧
            2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
              sourceFinalInformationConstant q (Δ / positiveNormalization 1 (Δ / 2) J) C_T Ce *
                (S.n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  obtain ⟨ct, Cent, eent, Cen, een, hct, htransport⟩ := exists_finiteFamilyTransportBound
  exact ⟨_, ct, Cent, eent, Cen, een,
    latticeTruncationRadiusConstant_pos R hΔ (by positivity : (0 : ℝ) ≤ C_T + 1), hct,
    sourceTarget_finalScale_mutualInformation_of_rounded_scales_explicit hq R hJ hΔ hC_T hC₁
      multiplicity hmultiplicity P hP hct htransport rfl⟩

open Classical in
/-- The concrete original-state information bound requires only the literal
rounded final scales, without separate doubled-radius, positive-separation
or four-separation hypotheses. The radius coefficient still precedes the
source entropy coefficient, and one size threshold precedes every physical
instance. All geometric and entropy premises are retained.
Source: `08-scanner.tex`, lines 32--58 and 808--941. -/
theorem exists_sourceTarget_finalScale_mutualInformation_of_rounded_scales
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
          let L := ⌊(S.n : ℝ) ^ (1 - (Exponents.scannerEll : ℝ))⌋₊
          let X := S.A.filter fun x ↦ x.val ∈ T
          let β := fun _ : Site Λ ↦ Fin q
          2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
              C * (S.n : ℝ) ^ (62497 / 62500 : ℝ) ∧
            2 * FiniteProduct.mutualInformation β Ω X (S.truncationSet L)ᶜ ≤
              C * (S.n : ℝ) ^ (1 - (Exponents.amplificationEpsilon : ℝ)) := by
  obtain ⟨Ctr, ct, Cent, eent, Cen, een, hCtr, -, hall⟩ :=
    exists_sourceTarget_finalScale_mutualInformation_of_rounded_scales_of_threshold_le hq R hJ hΔ
      hC_T hC₁ multiplicity hmultiplicity P hP
  exact ⟨Ctr, hCtr, fun Ce hCe => ⟨_, sourceFinalInformationConstant_pos hq _ hC_T hCe, _,
    two_le_sourceRoundedInformationThreshold _ _ _ _ _ _ _ _ _ _ _ _ _ _, hall Ce hCe⟩⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
