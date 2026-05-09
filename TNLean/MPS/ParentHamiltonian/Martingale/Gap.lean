/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Reduction

/-!
# Uniform spectral gap for the MPS parent Hamiltonian

**Root-only.** This file contains the capstone theorems that deliver the
uniform spectral gap for the MPS parent Hamiltonian. The remaining
Friedrichs-angle analytic estimate is the final missing proof obligation.

## Main results

* `parentHamiltonianES_gap_bound_of_friedrichs` — the MPS-specific
  Friedrichs-angle / row-sum estimate that supplies the remaining
  hypothesis for the reduction chain in `Martingale.Reduction`.
* `parentHamiltonian_gapped` — uniform spectral gap for MPS parent
  Hamiltonians on injective tensors, obtained from the Friedrichs-angle
  bound.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Uniform spectral gap for the MPS parent Hamiltonian -/

/- Scout report (2026-04-19, Layer 4 KL martingale).

1. **Friedrichs-angle surface:** TNLean currently has no dedicated
`FriedrichsAngle`/principal-angle development in `TNLean/Analysis`. Mathlib provides
orthogonal-projection structure (for example
`Mathlib.Analysis.InnerProductSpace.Projection.Basic` and
`Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`, exposing
`Submodule.starProjection` and `orthogonalProjection`) but not a ready-made
Kastoryano–Lucia-style angle-to-anticommutator bound. This is a real blocker
for quantitative overlap constants.
2. **Projection/positivity formulation:** the local `EuclideanSpace` projector
`parentInteractionES A L` and each transported local term are now available as
symmetric projections, and the conjugated cyclic-restriction summands
`localTermESSummand A hN L i τ = Rᵢ,τ† P_L Rᵢ,τ` plus the full transported
Hamiltonian are available as positive operators.
3. **Quadratic-form reduction:**
`parentHamiltonianES_norm_bound_of_quadratic_form` and
`parentHamiltonianES_gap_bound_of_quadratic_form` reduce the gap statement to a
uniform estimate `γ * re ⟪H_N v, v⟫ ≤ re ⟪H_N v, H_N v⟫`.
4. **Projection-geometry row reduction:**
`ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum`,
`parentHamiltonianES_quadratic_form_of_ordered_local_term_bounds`, and
`parentHamiltonianES_gap_bound_of_ordered_local_term_bounds` now formalize the
finite-sum algebra turning explicit ordered cross-term row bounds for local
symmetric projections into the quadratic-form hypothesis above.
5. **Remaining local analytic step:** local projection structure, cyclic-window
row cardinality, and non-overlap positivity are now formalized above. The remaining
hypothesis is the Friedrichs-angle estimate for overlapping cyclic windows with the
coefficient required by the finite-overlap row reduction.
6. **Spectral-gap theorem:** `parentHamiltonian_gapped` is the subsequent
existential theorem, now proved by applying the Friedrichs-angle theorem
below. The theorem `parentHamiltonianES_gap_bound_of_friedrichs` still depends
on the missing Friedrichs-angle formulation; this is the blocker and should not
be replaced with axioms or unrelated sorrys. -/
/-- Friedrichs-angle and row-sum estimate for the MPS parent Hamiltonian.

This is the remaining MPS-specific martingale estimate: it should produce a
specific uniform positive lower bound for the transported parent Hamiltonian
from the intersection property and finite-overlap geometry. The concrete
constant is intentionally part of this theorem statement, so the public
`parentHamiltonian_gapped` theorem only has to re-express it as an existential
spectral gap. -/
theorem parentHamiltonianES_gap_bound_of_friedrichs
    (A : MPSTensor d D) (_hA : IsInjective A) (L : ℕ) (_hL : 1 < L) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  -- Remaining obligation: prove the overlapping cyclic-window Friedrichs-angle
  -- estimate required by `parentHamiltonianES_gap_bound_of_cyclic_window_friedrichs`.
  -- Local projection structure, row cardinality, non-overlap positivity, kernel
  -- identification, and the spectral-theorem conversion are already formalized above.
  -- Proof obligation tracked by #952 and #460 (#190).
  sorry

/--
**Spectral gap for MPS parent Hamiltonians.**

For an injective MPS tensor `A` and interaction range `L > 1`, there exists
a uniform gap `γ > 0` (independent of system size `N`) such that for all
`N ≥ 2L`, every vector in the orthogonal complement of the ground space
satisfies `γ * ‖v‖ ≤ ‖H_ES v‖`.

The orthogonal complement is computed in the `EuclideanSpace` structure
on `NSiteSpace d N ≃ Cfg d N → ℂ`.

**Proof strategy (Kastoryano–Lucia 2018 / Nachtergaele 1996).** The parent
Hamiltonian `H_N = ∑ᵢ hᵢ` is a frustration-free sum of local orthogonal
projectors (`parentHamiltonian_frustrationFree`). The intersection property
`groundSpace_intersection` bounds the Friedrichs angle between adjacent local
ground spaces away from zero, which provides the martingale operator
inequality

    `h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)`

with constants `c_{ij}` depending only on the MPS tensor (not on `N`). At most
`2(L-1)` local terms overlap a given `h_i`, so the row-sum bound
`∑_{j≠i} c_{ij} ≤ 1` holds uniformly in `N`. Combined with `h_i^2 = h_i`,
this yields the quadratic-form inequality `H² ≥ γ H`, which feeds into
the abstract lemma `FrustrationFree.spectralGap_of_martingale` to produce
the norm bound `γ ‖v‖ ≤ ‖H v‖` on `(ker H)ᗮ`. The `LinearMap.IsPositive`
hypothesis required by `FrustrationFree.spectralGap_of_martingale` is
automatic here because `H_N = ∑ᵢ hᵢ` is a sum of orthogonal projectors.

The proof below invokes the MPS-specific Friedrichs-angle theorem
`parentHamiltonianES_gap_bound_of_friedrichs`, whose proof is the remaining
Friedrichs-angle and row-sum obligation. -/
theorem parentHamiltonian_gapped
    (A : MPSTensor d D) (hA : IsInjective A) (L : ℕ) (hL : 1 < L) :
    ∃ γ > 0, ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  obtain ⟨hγ, hgap⟩ := parentHamiltonianES_gap_bound_of_friedrichs A hA L hL
  exact ⟨(1 : ℝ) / (4 * (L : ℝ)), hγ, hgap⟩

end MPSTensor
