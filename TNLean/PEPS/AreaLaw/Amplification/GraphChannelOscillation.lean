/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.ComponentChannelOscillation
import TNLean.PEPS.AreaLaw.Amplification.ExponentialChannelShells

/-!
# Full graph channels with explicit stretched-exponential shell bounds

Exact support in the anchor's connected component identifies the full channel
with a sufficiently large finite-ball channel. Its oscillation bound therefore
inherits the explicit coefficients obtained from actual localization errors.
No infinite-series convention or analytic limit is used.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 101–139, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

variable {q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero q]
variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux]

/-- The full component-supported root channel has an explicit finite
stretched-exponential shell bound, with arbitrary finite spectators. Source:
area law, `eq:amplification-oscillation-increment`, lines 124–139, using exact
component stabilization. The cutoff need only contain the anchor component. -/
theorem siteOscillation_spectatorRootChannel_le_exp_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1)
    (n : ℕ) (hn : Finset.univ.sup (G.dist a) ≤ n)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (graphBall G a l) k‖ ≤
      C * Real.exp (-(c * (l : ℝ) ^ α)))
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (spectatorRootChannel k B) ≤ siteOscillation q y B +
      2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => G.edist a y ≤ l),
        ((2 + 8 * Real.sqrt C * Real.exp (c / 2)) *
          Real.exp (-(c / 2 * (l : ℝ) ^ α))) *
            ∑ z ∈ graphBall G a l, siteOscillation q z B := by
  have h := siteOscillation_localRootChannel_le_exp (graphBall G a) (graphBall_mono G a)
    hk₀ hk₁ hC hc hα hα₁ n hε y B
  simpa only [localRootChannel_graphBall_eq_of_component_support G a hk hn,
    mem_graphBall] using h

end TNLean.PEPS.AreaLaw
