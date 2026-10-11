/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Probability.PoissonWordSpatialGrowth
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordObservables
import TNLean.PEPS.AreaLaw.GraphExtendedMetric

/-!
# Spatial growth of physical channel words

The Poisson-word observable is the site oscillation of the actual chronological
composition of spectator root channels. The conversion by `List.ofFn` preserves
the empty word and appending an event. A supported initial matrix supplies the
initial indicator bound; the literal channel increment supplies the Poisson
recurrence. Thus the expected oscillation is integrable and has the spatial
exponential bound, with exact zero on components disjoint from the support.

The graph corollary derives the increment from positive contraction effects,
component support and localization tails up to an explicit finite cutoff. It
retains the weighted row hypothesis for the actual graph-ball event kernel.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–188, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Aux] [DecidableEq Aux]

/-- The Poisson-word concatenation applies the newly appended physical channel
after the entire prefix. Source: area law, `09-amplification.tex`, lines 161–173. -/
@[simp] theorem spectatorRootChannelWord_ofFn_append_singleton
    (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (u : PoissonWord.Word κ) (i : κ)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    spectatorRootChannelWord k
        (List.ofFn (PoissonWord.append u (PoissonWord.singleton i)).2) B =
      spectatorRootChannel (k i) (spectatorRootChannelWord k (List.ofFn u.2) B) := by
  simp only [PoissonWord.append, List.ofFn_fin_append, PoissonWord.ofFn_singleton,
    spectatorRootChannelWord_append_singleton]

variable [Fintype κ] [NeZero q]

/-- A weighted graph kernel controlling the literal one-step physical
oscillations gives integrability, expected spatial decay and exact vanishing
at infinite distance from the initial support. The initial coefficient is
derived from the supported physical blocks of `B`, with no Hermiticity or
nonempty spectator hypothesis. Source: area law, `09-amplification.tex`,
lines 161–188. -/
theorem integrable_and_integral_siteOscillation_le_of_graph_kernel
    (G : SimpleGraph ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (A : ι → ι → ℝ) {β α v : ℝ}
    (hβ : 0 ≤ β) (hα : 0 < α) (hα₁ : α ≤ 1) (hv : 0 ≤ v)
    (hA : ∀ y z, 0 ≤ A y z)
    (hstep : ∀ (y : ι)
      (W : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ),
      (∑ i, (siteOscillation q y (spectatorRootChannel (k i) W) -
        siteOscillation q y W)) ≤ ∑ z, A y z * siteOscillation q z W)
    (hcomponent : ∀ y z, ¬ G.Reachable y z → A y z = 0)
    (hrow : ∀ y, (∑ z, A y z * Real.exp (β * (G.dist y z : ℝ) ^ α)) ≤ v)
    (S : Finset ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (hB : ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (S : Set ι)) (t : ℝ≥0) (y : ι) :
    letI := graphPseudoEMetricSpace G
    Integrable (fun u : PoissonWord.Word κ =>
        siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B))
      (PoissonWord.measure κ t) ∧
      (∫ u, siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B)
        ∂PoissonWord.measure κ t) ≤
        Real.exp (v * t) * (2 * ‖B‖) *
          Metric.exponentialDistanceProfile (S : Set ι) β α y ∧
      (∀ u : PoissonWord.Word κ, Metric.infEDist y (S : Set ι) = ⊤ →
        siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B) = 0) := by
  let := graphPseudoEMetricSpace G
  let f (u : PoissonWord.Word κ) (z : ι) :=
    siteOscillation q z (spectatorRootChannelWord k (List.ofFn u.2) B)
  have hf (u : PoissonWord.Word κ) (z : ι) : 0 ≤ f u z :=
    siteOscillation_nonneg z _
  have hnorm : 0 ≤ 2 * ‖B‖ := by positivity
  have hinitial (z : ι) :
      f PoissonWord.nil z ≤ 2 * ‖B‖ * (S : Set ι).indicator (fun _ => (1 : ℝ)) z := by
    simpa only [f, PoissonWord.nil, List.ofFn_zero, spectatorRootChannelWord_nil] using
      siteOscillation_le_support_indicator S B hB z
  have hword (u : PoissonWord.Word κ) (z : ι) :
      (∑ i, (f (PoissonWord.append u (PoissonWord.singleton i)) z - f u z)) ≤
        ∑ x, A z x * f u x := by
    simpa only [f, spectatorRootChannelWord_ofFn_append_singleton] using
      hstep z (spectatorRootChannelWord k (List.ofFn u.2) B)
  have hsupport (z x : ι) (hzx : edist z x = ⊤) : A z x = 0 :=
    hcomponent z x ((graphPseudoEMetricSpace_edist_eq_top G z x).mp hzx)
  have hmetric (z : ι) :
      (∑ x, A z x * Real.exp (β * (edist z x).toReal ^ α)) ≤ v := by
    simpa only [graphPseudoEMetricSpace_edist_toReal] using hrow z
  have h := PoissonWord.integrable_and_integral_le_of_spatial_growth t f A (S : Set ι)
    hβ hα hα₁ hf hA hv hnorm hinitial hword hsupport hmetric y
  refine ⟨h.1, h.2, fun u hy => ?_⟩
  exact PoissonWord.eq_zero_of_spatial_growth_of_infEDist_eq_top f A (S : Set ι)
    hβ hα hα₁ hf hA hv hnorm hinitial hword hsupport hmetric y hy u

/-- The expected site oscillation of the actual physical channel word, from
component-supported positive contractions and their localization tails. The
cutoff covers every retained anchor, and the assumed row bound is for the
literal graph-ball incidence kernel with the derived tail coefficient.
Source: area law, `09-amplification.tex`, lines 139–188. -/
theorem integrable_and_integral_siteOscillation_le_graphChannelEventKernel
    (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk₁ : ∀ i, k i ≤ 1)
    (hk : ∀ i, k i ∈ supportedOperators q {x | G.Reachable (a i) x})
    {C c α v : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hv : 0 ≤ v) (N : ℕ) (hN : ∀ i, Finset.univ.sup (G.dist (a i)) ≤ N)
    (hε : ∀ i l, l ≤ N → ‖k i - siteExpectation q (graphBall G (a i) l) (k i)‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (hrow : ∀ y, (∑ z,
      graphChannelEventKernel G a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
        (c / 2) α N y z *
          Real.exp (c / (4 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) ≤ v)
    (S : Finset ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ)
    (hB : ∀ a b : Aux, (Matrix.of fun σ τ => B (σ, a) (τ, b)) ∈
      supportedOperators q (S : Set ι)) (t : ℝ≥0) (y : ι) :
    letI := graphPseudoEMetricSpace G
    Integrable (fun u : PoissonWord.Word κ =>
        siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B))
      (PoissonWord.measure κ t) ∧
      (∫ u, siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B)
        ∂PoissonWord.measure κ t) ≤
        Real.exp (v * t) * (2 * ‖B‖) * Metric.exponentialDistanceProfile
          (S : Set ι) (c / (4 * (2 : ℝ) ^ α)) α y ∧
      (∀ u : PoissonWord.Word κ, Metric.infEDist y (S : Set ι) = ⊤ →
        siteOscillation q y (spectatorRootChannelWord k (List.ofFn u.2) B) = 0) := by
  apply integrable_and_integral_siteOscillation_le_of_graph_kernel G k
    (graphChannelEventKernel G a (2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2)))
      (c / 2) α N) (by positivity) hα hα₁ hv
    (graphChannelEventKernel_nonneg G a (by positivity) (c / 2) α N)
    (sum_siteOscillation_spectatorRootChannel_sub_le_graphChannelEventKernel
      G a k hk₀ hk₁ hk hC hc hα hα₁ N hN hε)
    (graphChannelEventKernel_eq_zero_of_not_reachable G a _ _ _ _) hrow S B hB t y

end TNLean.PEPS.AreaLaw
