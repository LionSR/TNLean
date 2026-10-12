/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.ProjectedRelativeEvolution
import TNLean.PEPS.AreaLaw.RegionOperatorLocalization
import QICLean.Analysis.GaussianFilter.MatrixIntegral

/-!
# A supported Gaussian approximation between two Hamiltonians

Project both the evolved observable and the relative-evolution generator
onto the same graph neighbourhood. The projected differential equation
constructs a unitary path on this neighbourhood. Integrating the product
against the original restricted Gaussian measure gives a supported
operator, with norm and approximation bounds uniform in the variance.

The path is chosen before the variance and time cutoff. Neither a
propagator nor an approximating operator is supplied as a hypothesis.
Only the actual supports of the input observable and Hamiltonian
difference enter. No spectral gap or information assumption is used.

## References

OpenAI, Polynomial PEPS approximation of gapped square-grid ground states,
September 24, 2026, Section 2, lines 513–562, in the proof of
eq:info-local-two-sided. Source revision:
openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The common projection region is the neighbourhood of the union of the
two input supports, as in the support conclusion of that argument.
Independently formalized; no upstream Lean proof text is reused.
-/

open MeasureTheory ProbabilityTheory QuantumCircuit
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace TNLean.PEPS.AreaLaw

/-- The actual projected relative evolution constructs a supported
approximation to every truncated two-Hamiltonian Gaussian filter.
The same path works for all variances and nonnegative time cutoffs.
Source: polynomial-PEPS, Section 2, eq:info-local-two-sided,
lines 513–562. -/
theorem exists_supported_gaussian_integral (q : ℕ) (hq : 1 ≤ q)
    (R : ℕ) (J : ℝ) :
    ∃ C v c : ℝ, 0 < C ∧ 0 < v ∧ 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (g : LocalHamiltonian Λ q R J)
        (H W : Matrix (Configuration Λ q) (Configuration Λ q) ℂ),
        H.IsHermitian →
        ∀ Q Z : Finset (Site Λ),
          W ∈ supportedOperators q (Q : Set (Site Λ)) →
          g.operator - H ∈ supportedOperators q (Z : Set (Site Λ)) →
          ∀ l : ℕ,
            let B := graphNeighborhood Λ l (Q ∪ Z)
            ∃ U : ℝ → Matrix (Configuration Λ q) (Configuration Λ q) ℂ,
              U 0 = 1 ∧
              (∀ t, HasDerivAt U
                ((Complex.I • siteExpectation q B
                  (heisenbergEvolution g.operator t (g.operator - H))) * U t) t) ∧
              (∀ t, U t ∈ Matrix.unitaryGroup (Configuration Λ q) ℂ) ∧
              (∀ t, U t ∈ supportedOperators q (B : Set (Site Λ))) ∧
              ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
                let M := ∫ t : ℝ in Set.Icc (-T) T,
                  siteExpectation q B (heisenbergEvolution g.operator t W) * U t
                    ∂gaussianReal 0 η
                M ∈ supportedOperators q (B : Set (Site Λ)) ∧
                ‖M‖ ≤ ‖W‖ ∧
                ‖M - GaussianFilter.gaussianIntertwinerTruncated η T g.operator H W‖ ≤
                  ‖W‖ * C * (Λ.card : ℝ) * (1 + ‖g.operator - H‖ * T) *
                    Real.exp (v * T - c * l) := by
  classical
  obtain ⟨C, v, c, hC, hv, hc, hlocal⟩ :=
    exists_quasilocal_region_localization q hq R J
  refine ⟨C, v, c, hC, hv, hc, ?_⟩
  done

end TNLean.PEPS.AreaLaw
