/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelPoissonGrowth
import TNLean.PEPS.AreaLaw.Amplification.LatticeChannelWeightedRow

/-!
# Expected spatial oscillation for retained lattice channel words

The actual positive constraints of the filtered lattice Hamiltonian define
chronological spectator root-channel words. Their site oscillations, started
from a supported operator, are integrable under the retained Poisson-word law
and satisfy the spatial exponential estimate. The constants are chosen before
the domain, local dimension, Hamiltonian, retained labels and spectator.

The finite cutoff is chosen internally by taking the maximum component radius
over retained anchors. The existing lattice channel kernel theorem supplies
both the literal physical increment and its uniform weighted row bound.
Disconnected components retain infinite distance and zero oscillation.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–188, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit SpectralFilter Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- The actual retained lattice channel evolution satisfies the expected
spatial oscillation bound. The constants depend only on `p, R, J, Δ`, and the
spatial weight is `c / (4 * 2 ^ kernelExponent p)`. Neither localization tails,
ball growth, label multiplicity, a weighted row estimate nor integrability is
assumed. Empty retained families, empty domains and empty spectators are
allowed. Source: area law, `09-amplification.tex`, lines 161–188, using the
actual kernel bounds at lines 139–160. -/
theorem exists_latticeChannelWord_spatial_growth {p : ℕ} (hp : 1 ≤ p)
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
        let k := fun i : {i // P i} => positiveConstraint (positiveNormalization p (Δ / 2) J)
          (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        Integrable (fun u : PoissonWord.Word {i // P i} =>
            siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B))
          (PoissonWord.measure {i // P i} t) ∧
          (∫ u, siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B)
            ∂PoissonWord.measure {i // P i} t) ≤
            Real.exp (v * t) * (2 * ‖B‖) * Metric.exponentialDistanceProfile
              (S : Set (Site Λ)) (c / (4 * (2 : ℝ) ^ α)) α y ∧
          (∀ u : PoissonWord.Word {i // P i}, Metric.infEDist y (S : Set (Site Λ)) = ⊤ →
            siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B) = 0) := by
  obtain ⟨C, c, v, hC, hc, hv, hbounds⟩ := exists_latticeChannelEventKernel_bounds hp R hJ hΔ
  refine ⟨c, v, hc, hv, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs P _ Aux _ _ S B hB t y
  let α := kernelExponent p
  let aP := fun i : {i // P i} => a i
  let k := fun i : {i // P i} => positiveConstraint (positiveNormalization p (Δ / 2) J)
    (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
  let N := Finset.univ.sup fun i : {i // P i} =>
    Finset.univ.sup ((domainGraph Λ).dist (a i))
  have hN (i : {i // P i}) : Finset.univ.sup ((domainGraph Λ).dist (a i)) ≤ N :=
    Finset.le_sup (f := fun i : {i // P i} =>
      Finset.univ.sup ((domainGraph Λ).dist (a i))) (Finset.mem_univ i)
  obtain ⟨hrow, hstep⟩ := hbounds Λ h a ha E₀ Ω hgs P Aux N hN
  exact integrable_and_integral_siteOscillation_le_of_graph_kernel (domainGraph Λ) k
    (graphChannelEventKernel (domainGraph Λ) aP
      (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2))) (c / 2) α N)
    (by positivity) (kernelExponent_pos hp) (kernelExponent_le_one p) hv
    (graphChannelEventKernel_nonneg (domainGraph Λ) aP (by positivity) (c / 2) α N)
    hstep (graphChannelEventKernel_eq_zero_of_not_reachable (domainGraph Λ) aP _ _ _ _)
    hrow S B hB t y

end TNLean.PEPS.AreaLaw
