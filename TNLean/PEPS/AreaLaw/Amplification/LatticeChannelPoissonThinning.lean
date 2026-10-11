/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordThinning
import TNLean.PEPS.AreaLaw.Amplification.LatticeChannelPoissonGrowth

/-!
# Spatial growth after filtering a full lattice Poisson word

The expected spatial oscillation bound for retained lattice channels also
holds when the sample is a full-alphabet Poisson word and the omitted events
are deleted. Filtering preserves the chronological order of all retained
events. Its fixed-time marginal law is the retained Poisson-word law, so both
integrability and the expected bound transfer with the same constants.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 161–188, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit SpectralFilter Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- Filtering the actual full Poisson sample gives the same uniform spatial
bound as sampling the retained alphabet. The effects are still constructed
from the original Hamiltonian. Constants precede the domain, local dimension,
retained predicate, spectator and supported initial matrix. This is a
fixed-time word-law statement. Source: area law, `09-amplification.tex`,
lines 161–188. -/
theorem exists_latticeChannelWord_filter_spatial_growth {p : ℕ} (hp : 1 ≤ p)
    (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c v : ℝ, 0 < c ∧ 0 ≤ v ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (P : AdmissibleSupport Λ R → Prop) [DecidablePred P]
          (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (S : Finset (Site Λ))
          (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
        (∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
          supportedOperators q (S : Set (Site Λ))) →
        ∀ (t : ℝ≥0) (y : Site Λ),
        letI := graphPseudoEMetricSpace (domainGraph Λ)
        let α := kernelExponent p
        let k := fun i : AdmissibleSupport Λ R =>
          positiveConstraint (positiveNormalization p (Δ / 2) J)
            (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        Integrable (fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
            siteOscillation q y (spectatorRootChannelWord k
              ((List.ofFn w.2).filter (fun i => decide (P i))) B))
          (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
          (∫ w, siteOscillation q y (spectatorRootChannelWord k
              ((List.ofFn w.2).filter (fun i => decide (P i))) B)
            ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
            Real.exp (v * t) * (2 * ‖B‖) * Metric.exponentialDistanceProfile
              (S : Set (Site Λ)) (c / (4 * (2 : ℝ) ^ α)) α y ∧
          (∀ w : PoissonWord.Word (AdmissibleSupport Λ R),
            Metric.infEDist y (S : Set (Site Λ)) = ⊤ →
            siteOscillation q y (spectatorRootChannelWord k
              ((List.ofFn w.2).filter (fun i => decide (P i))) B) = 0) := by
  obtain ⟨c, v, hc, hv, hgrowth⟩ := exists_latticeChannelWord_spatial_growth hp R hJ hΔ
  refine ⟨c, v, hc, hv, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs P _ Aux _ _ S B hB t y
  let := graphPseudoEMetricSpace (domainGraph Λ)
  let k := fun i : AdmissibleSupport Λ R =>
    positiveConstraint (positiveNormalization p (Δ / 2) J)
      (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
  have hg := hgrowth Λ h a ha E₀ Ω hgs P Aux S B hB t y
  have htransport := integrable_and_integral_siteOscillation_filter_le P k B t y _
    ⟨hg.1, hg.2.1⟩
  refine ⟨htransport.1, htransport.2, fun w hy => ?_⟩
  rw [spectatorRootChannelWord_filter]
  exact hg.2.2 (PoissonWord.partitionWords P w).1 hy

end TNLean.PEPS.AreaLaw
