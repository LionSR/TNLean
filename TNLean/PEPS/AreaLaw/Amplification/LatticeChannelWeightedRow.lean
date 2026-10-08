/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelWeightedRow
import TNLean.PEPS.AreaLaw.LatticeConstraints

/-!
# Actual channel-family weighted rows on a finite lattice domain

The literal positive constraints produced from the filtered lattice Hamiltonian
satisfy the finite channel-increment and weighted row estimates, uniformly in
the domain, local dimension, spectator dimension and finite cutoff. The graph
ball and anchor multiplicity bounds are supplied by the existing lattice
counts. The scalar constants are chosen from the original positive-constraint
tails before any lattice or operator data; square-root tail constants are not
used here.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`09-amplification.tex`, lines 139–160, using the positive constraints in
`03-quasilocal.tex`, lines 220–246, and the lattice counts in
`01-preliminaries.tex`, lines 82–103, at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean text is reused.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open QuantumCircuit SpectralFilter Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.PEPS.AreaLaw

/-- Actual positive-constraint channels on an induced lattice domain have a
uniform finite weighted row bound and satisfy literal summed oscillation
increment domination, also with arbitrary finite spectators. The witnesses
`C ≥ 0`, `c > 0` and `v ≥ 0` depend only on `p, R, J, Δ`: they precede the
local dimension, domain, Hamiltonian, anchors, ground vector, spectator and
cutoff. The kernel uses the original effect-tail constants, with
`D = 2 * (2 + 8 * sqrt C * exp (c / 2))`, `b = c / 2`, and weight exponent
`c / (4 * 2 ^ kernelExponent p)`. Ball growth is `K = 2` and anchor
multiplicity is `μ = 2 ^ (1 + 2 * R * (R + 1) - 1)`; neither is assumed.
Source: area law, `09-amplification.tex`, lines 139–160, with Proposition 4.3,
`03-quasilocal.tex`, lines 220–246. -/
theorem exists_latticeChannelEventKernel_bounds {p : ℕ} (hp : 1 ≤ p)
    (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c v : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 ≤ v ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (N : ℕ),
        (∀ i, Finset.univ.sup ((domainGraph Λ).dist (a i)) ≤ N) →
        let α := kernelExponent p
        let k := fun i => positiveConstraint (positiveNormalization p (Δ / 2) J)
          (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        let D := 2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2))
        (∀ y, (∑ z, graphChannelEventKernel (domainGraph Λ) a D (c / 2) α N y z *
          Real.exp (c / (4 * (2 : ℝ) ^ α) * ((domainGraph Λ).dist y z : ℝ) ^ α)) ≤ v) ∧
        (∀ (y : Site Λ)
            (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∑ i, (siteOscillation q y (spectatorRootChannel (k i) B) -
            siteOscillation q y B)) ≤
          ∑ z, graphChannelEventKernel (domainGraph Λ) a D (c / 2) α N y z *
            siteOscillation q z B) := by
  obtain ⟨C, c, hC, hc, hpos⟩ := exists_latticePositiveConstraints hp R hJ hΔ
  obtain ⟨v, hv, hbounds⟩ := exists_graphChannelEventKernel_bounds_of_component_support
    hC (K := 2) zero_le_two
    (μ := ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)) (Nat.cast_nonneg _)
    hc (kernelExponent_pos hp) (kernelExponent_le_one p)
  refine ⟨C, c, v, hC, hc, hv, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs Aux _ _ N hN α k D
  obtain ⟨-, hk, -, -, -, htail, hcomp⟩ := hpos Λ h a ha E₀ Ω hgs
  exact hbounds (Site Λ) (AdmissibleSupport Λ R) Aux q (domainGraph Λ) a k
    (fun i => (hk i).1) (fun i => (hk i).2.1) hcomp card_graphBall_domainGraph_le
    (fun x => by exact_mod_cast card_anchor_fiber_le a ha x) N hN
    (fun i l _ => (htail i l).2.2)

end TNLean.PEPS.AreaLaw
