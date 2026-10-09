/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LiebRobinson.GraphBallStabilization
import TNLean.PEPS.AreaLaw.Amplification.LocalChannelOscillation

/-!
# Full-channel oscillation from exact component support

An operator supported on the anchor's connected component is fixed by graph
ball expectations once the ball contains that component. Consequently its
localized root channel equals its full root channel at every sufficiently
large finite radius. This transfers the finite-shell oscillation estimate
without an analytic limit or a tail hypothesis. A site at infinite distance
from the anchor cannot have its oscillation increased.

All channel statements allow arbitrary finite spectators and arbitrary,
not necessarily Hermitian, observables, with no spectator dimension factor.
The graph is the supplied finite graph, so an induced domain retains its own
geometry.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 124–139, at revision
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

/-- Component support makes every sufficiently large ball expectation exact.
Source: area law, `09-amplification.tex`, lines 135–139. -/
theorem siteExpectation_graphBall_eq_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {n : ℕ} (hn : Finset.univ.sup (G.dist a) ≤ n) :
    siteExpectation q (graphBall G a n) k = k := by
  apply siteExpectation_of_mem_supportedOperators
  rwa [coe_graphBall_eq_reachable_of_sup_dist_le G a hn]

/-- The actual localization error vanishes beyond the component cutoff.
Source: area law, `09-amplification.tex`, lines 135–139. -/
theorem norm_sub_siteExpectation_graphBall_eq_zero_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {n : ℕ} (hn : Finset.univ.sup (G.dist a) ≤ n) :
    ‖k - siteExpectation q (graphBall G a n) k‖ = 0 := by
  rw [siteExpectation_graphBall_eq_of_component_support G a hk hn, sub_self, norm_zero]

/-- Component support makes the localized and full root channels equal at
all sufficiently large finite radii. Source: area law,
`09-amplification.tex`, lines 124–139. -/
theorem localRootChannel_graphBall_eq_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {n : ℕ} (hn : Finset.univ.sup (G.dist a) ≤ n)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannel (graphBall G a n) k B = spectatorRootChannel k B := by
  rw [localRootChannel, siteExpectation_graphBall_eq_of_component_support G a hk hn]

/-- A single finite radius gives exact expectation and channel stabilization,
uniformly over all spectator observables. Source: area law,
`09-amplification.tex`, lines 135–139. -/
theorem exists_localRootChannel_graphBall_eq_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ supportedOperators q {x | G.Reachable a x}) :
    ∃ N, ∀ n ≥ N, siteExpectation q (graphBall G a n) k = k ∧
      ∀ B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ,
        localRootChannel (graphBall G a n) k B = spectatorRootChannel k B :=
  ⟨Finset.univ.sup (G.dist a), fun _ hn =>
    ⟨siteExpectation_graphBall_eq_of_component_support G a hk hn,
      localRootChannel_graphBall_eq_of_component_support G a hk hn⟩⟩

/-- Every successor shell beyond the component cutoff is exactly zero.
Source: area law, `09-amplification.tex`, lines 124–139. -/
theorem localRootChannelShell_graphBall_succ_eq_zero_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    {n : ℕ} (hn : Finset.univ.sup (G.dist a) ≤ n)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    localRootChannelShell (graphBall G a) k (n + 1) B = 0 := by
  rw [localRootChannelShell,
    localRootChannel_graphBall_eq_of_component_support G a hk (hn.trans (Nat.le_succ n)),
    localRootChannel_graphBall_eq_of_component_support G a hk hn, sub_self]

/-- The full root channel satisfies the finite-shell increment once the cutoff
contains the anchor's component. Only actual localization errors up to that
finite cutoff are needed. Source: area law,
`eq:amplification-oscillation-increment`, lines 124–139. -/
theorem siteOscillation_spectatorRootChannel_le_of_component_support
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    (ε : ℕ → ℝ) (n : ℕ) (hn : Finset.univ.sup (G.dist a) ≤ n)
    (hε : ∀ l ≤ n, ‖k - siteExpectation q (graphBall G a l) k‖ ≤ ε l)
    (y : ι) (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (spectatorRootChannel k B) ≤ siteOscillation q y B +
      2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => G.edist a y ≤ l),
        localRootChannelShellBound ε l * ∑ z ∈ graphBall G a l, siteOscillation q z B := by
  have h := siteOscillation_localRootChannel_le (graphBall G a) (graphBall_mono G a)
    hk₀ hk₁ ε n hε y B
  simpa only [localRootChannel_graphBall_eq_of_component_support G a hk hn,
    mem_graphBall] using h

/-- A component-supported full channel cannot increase oscillation at a site
in a different component. Source: area law,
`09-amplification.tex`, lines 133–139. -/
theorem siteOscillation_spectatorRootChannel_le_of_edist_eq_top
    (G : SimpleGraph ι) (a : ι) {k : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1)
    (hk : k ∈ supportedOperators q {x | G.Reachable a x})
    (y : ι) (hy : G.edist a y = ⊤)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) :
    siteOscillation q y (spectatorRootChannel k B) ≤ siteOscillation q y B := by
  let n := Finset.univ.sup (G.dist a)
  rw [← localRootChannel_graphBall_eq_of_component_support G a hk (n := n) le_rfl B]
  exact siteOscillation_localRootChannel_le_of_notMem (graphBall G a n) hk₀ hk₁ y
    (notMem_graphBall_of_edist_eq_top hy n) B

end TNLean.PEPS.AreaLaw
