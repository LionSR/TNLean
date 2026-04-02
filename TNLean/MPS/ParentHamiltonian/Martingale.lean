/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.Basic
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.MPS.ParentHamiltonian.IntersectionProperty

/-!
# Martingale-method spectral-gap scaffolding for parent Hamiltonians

This file introduces a first formal scaffold for the martingale approach to proving
that MPS parent Hamiltonians are gapped.

The intended proof route is:
1. frustration-freeness (`parentHamiltonian_frustrationFree`),
2. local projector gap (`parentInteraction`/`localTerm` as orthogonal projections),
3. intersection property (`groundSpace_intersection`),
4. a martingale estimate (Nachtergaele / Kastoryano–Lucia).

The final quantitative assembly is left as future work.

## Main results

* `parentHamiltonian_gapped` — spectral gap: vectors in the orthogonal complement
  of the ground space satisfy `⟨v, Hv⟩ ≥ γ ⟨v, v⟩` with a uniform gap `γ > 0`.
-/

namespace MPSTensor

open scoped BigOperators InnerProductSpace

variable {d D : ℕ}

/-- Ground-space submodule for the finite-size parent Hamiltonian,
transported to the `EuclideanSpace` (inner-product) setting so that
orthogonal complements are available. -/
noncomputable def parentHamiltonianGroundSpaceES (A : MPSTensor d D)
    (L N : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Cfg d N)) :=
  (LinearMap.ker (parentHamiltonian A L N)).map
    (WithLp.linearEquiv 2 ℂ (NSiteSpace d N)).symm.toLinearMap

/-- The parent Hamiltonian transported to `EuclideanSpace`. -/
noncomputable def parentHamiltonianES (A : MPSTensor d D) (L N : ℕ) :
    EuclideanSpace ℂ (Cfg d N) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d N) :=
  let e := (WithLp.linearEquiv 2 ℂ (NSiteSpace d N))
  e.symm.toLinearMap.comp ((parentHamiltonian A L N).comp e.toLinearMap)

/--
**Spectral gap for MPS parent Hamiltonians.**

For an injective MPS tensor `A` and interaction range `L > 1`, there exists
a uniform gap `γ > 0` (independent of system size `N`) such that every
vector in the orthogonal complement of the ground space satisfies
`‖H_ES v‖ ≥ γ * ‖v‖`.

The orthogonal complement is computed in the `EuclideanSpace` structure
on `NSiteSpace d N ≃ Cfg d N → ℂ`.

TODO: prove via martingale estimate (Nachtergaele / Kastoryano–Lucia). -/
theorem parentHamiltonian_gapped
    (A : MPSTensor d D) (hA : IsInjective A) (L : ℕ) (hL : 1 < L) :
    ∃ γ > 0, ∀ (N : ℕ) (hLN : L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ‖parentHamiltonianES A L N v‖ ≥ γ * ‖v‖ := by
  sorry

end MPSTensor
