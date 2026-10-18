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
  classical
  obtain ⟨Ctr, hCtr, hsource⟩ := exists_sourceTarget_finalScale_mutualInformation
    hq R hJ hΔ hC_T hC₁ multiplicity hmultiplicity P hP
  obtain ⟨Ng, hNg, hgeometry⟩ := exists_finalScanner_admissibility hCtr.le
  refine ⟨Ctr, hCtr, ?_⟩
  intro Ce hCe
  obtain ⟨C, hC, N, hN, hbound⟩ := hsource Ce hCe
  refine ⟨C, hC, max N Ng, hN.trans (le_max_left _ _), ?_⟩
  intro Λ T _ hT h S E₀ Ω hgs hgraph hanchor hn hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix
  have hnN : N ≤ S.n := (le_max_left N Ng).trans hn
  have hnG : Ng ≤ S.n := (le_max_right N Ng).trans hn
  have hscales := hgeometry S.n hnG
  simp only [roundedLogRadius, ← hmScale, ← hDScale, ← hKScale, ← hr] at hscales
  exact hbound Λ T hT h S E₀ Ω hgs hgraph hanchor hnN hr hmScale hDScale hKScale
    hCeq hsize hdepth hrows hmult hclear htargetEntropy hprefix
    hscales.1 hscales.2.1 hscales.2.2.1

end TNLean.PEPS.AreaLaw.Scan.CollarScan
