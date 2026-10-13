/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PhysicalBufferCoordinates
import TNLean.PEPS.Approximation.SwappedSquareHamiltonianBoundary
import TNLean.PEPS.Approximation.SwappedSquareHamiltonianInteraction
import TNLean.PEPS.AreaLaw.SupportedGaussianIntegral

/-!
# A supported Gaussian buffer operator for the square Hamiltonian

The original square Hamiltonian and its actual partial swap determine the two
generators. The canonical regional split identifies the grouped buffer operator
with its lift from the physical complement. The resulting supported integral
uses the actual projected relative evolution and the original Gaussian measure.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 498–564,
`eq:info-operator-localization` and `eq:info-local-two-sided`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix MeasureTheory ProbabilityTheory QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator NNReal

namespace TNLean.PEPS.Approximation

/-- The actual square Hamiltonian and grouped buffer matrix construct a
supported Gaussian approximation. Both spatial support hypotheses are derived
from the original interactions and coordinate maps. The constants precede all
finite systems, and the same relative path precedes every variance and cutoff.
Source: polynomial-PEPS, Section 2, `eq:info-local-two-sided`, lines 513–562. -/
theorem SquareHamiltonian.exists_supported_buffer_gaussian_integral
    (q : ℕ) (hq : 1 ≤ q) (J : ℝ) (hJ : 0 ≤ J) :
    ∃ C v c : ℝ, 0 < C ∧ 0 < v ∧ 0 < c ∧
      ∀ (L : ℕ) (h : SquareHamiltonian L q J)
        (R C₀ : Finset (SquareLatticeVertex L L)) (hRC : Disjoint R C₀),
        let Q := (R ∪ C₀)ᶜ
        let P := Fin (Fintype.card (R → Fin q)) × Fin (Fintype.card (C₀ → Fin q))
        let s := FiniteProduct.splitTwoRegionsEquiv
          (fun _ : SquareLatticeVertex L L ↦ Fin q) R C₀ hRC
        let g := (s.prodCongr s).trans (Equiv.doubledRegroup P (Q → Fin q))
        let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
        let Λ := AreaLaw.rectangularDomain L L
        let a := AreaLaw.rectangleSiteEquiv L L
        let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
        let K := reindex (p.trans e) (p.trans e) (doubledHamiltonian h.operator)
        let F := reindex (p.trans e) (p.trans e) (EncodedFrame.sheetSwapOp q R)
        let K' := F * K * Fᴴ
        let boundary : Finset (Edge (squareLatticeGraph L L)) :=
          Finset.univ.filter (IsRegionBoundaryEdge R)
        let Z := boundary.biUnion fun b ↦
          ({b.1.1, b.1.2} : Finset (SquareLatticeVertex L L))
        ∀ W : Matrix ((Q → Fin q) × (Q → Fin q)) ((Q → Fin q) × (Q → Fin q)) ℂ,
          let V := reindex (g.symm.trans (p.trans e)) (g.symm.trans (p.trans e))
            ((1 : Matrix (P × P) (P × P) ℂ) ⊗ₖ W)
          ∀ l : ℕ,
            let B := AreaLaw.graphNeighborhood Λ l (Q.image a ∪ Z.image a)
            ∃ U : ℝ → Matrix (AreaLaw.Configuration Λ (q * q))
                (AreaLaw.Configuration Λ (q * q)) ℂ,
              U 0 = 1 ∧
              (∀ t, HasDerivAt U
                ((Complex.I • siteExpectation (q * q) B
                  (heisenbergEvolution K' t (K' - K))) * U t) t) ∧
              (∀ t, U t ∈ unitaryGroup (AreaLaw.Configuration Λ (q * q)) ℂ) ∧
              (∀ t, U t ∈ supportedOperators (q * q) (B : Set (AreaLaw.Site Λ))) ∧
              ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
                let M := ∫ t : ℝ in Set.Icc (-T) T,
                  siteExpectation (q * q) B (heisenbergEvolution K' t V) * U t
                    ∂gaussianReal 0 η
                M ∈ supportedOperators (q * q) (B : Set (AreaLaw.Site Λ)) ∧
                ‖M‖ ≤ ‖W‖ ∧
                ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K V‖ ≤
                  ‖W‖ * C * (L : ℝ) ^ 2 * (1 + 8 * J * (L : ℝ) ^ 2 * T) *
                    Real.exp (v * T - c * l) := by
  classical
  obtain ⟨C, v, c, hC, hv, hc, hgauss⟩ :=
    AreaLaw.exists_supported_gaussian_integral (q * q)
      (Nat.mul_le_mul hq hq) 1 (2 * J)
  refine ⟨C, v, c, hC, hv, hc, fun L h R C₀ hRC ↦ ?_⟩
  intro Q P s g p Λ a e K F K' boundary Z W V l B
  obtain ⟨gH, _, hgOperator⟩ := h.exists_swapped_doubled_localHamiltonian hJ R
  done

end TNLean.PEPS.Approximation
