/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Defs
import TNLean.MPS.ParentHamiltonian.Basic

/-!
# Martingale-method spectral-gap framework for parent Hamiltonians

This file sets up the martingale approach to proving
that MPS parent Hamiltonians are gapped, following
Kastoryano–Lucia 2018 (arXiv:1705.09491), Nachtergaele 1996
(Comm. Math. Phys. 175, 565), and Fannes–Nachtergaele–Werner 1992.

## Proof route

1. **Frustration-freeness** (`parentHamiltonian_frustrationFree`): every local
   term annihilates the MPV ground state.
2. **Local projector structure** (`parentInteraction`/`localTerm`): each local
   term is an orthogonal projector on its `L`-site window.
3. **Intersection property** (`groundSpace_intersection`, proved in PR #265):
   for an injective MPS tensor, the kernel of the sum of two overlapping local
   terms equals the intersection of their kernels.
4. **Martingale operator bound**: the intersection property gives a positive
   Friedrichs angle between adjacent local ground spaces, which is the
   quantitative content of

        `h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)`

   with constants `c_{ij}` depending only on the MPS tensor, not on `N`.
5. **Row-sum bound** `∑_{j ≠ i} c_{ij} ≤ 1`: at most `2(L-1)` local terms
   overlap a given local term.
6. **Quadratic form ⟹ norm bound**: the above yields `H² ≥ γ H` as operators,
   which by the spectral theorem gives `γ ‖v‖ ≤ ‖H v‖` for `v ⊥ ker H`.

The heavy lifting — deriving the norm bound `γ ‖v‖ ≤ ‖H v‖` on `(ker H)ᗮ`
from the MPS-specific operator inequality — is all contained in
`parentHamiltonian_gapped`, which is currently left as `sorry`. A small
self-contained helper `spectralGap_norm_bound_to_eigenvalue` records the
elementary final conversion from that norm bound to an eigenvalue-level gap
statement; it is the only part of the chain that admits a short proof, and is
proved here unconditionally.

## Main results

* `spectralGap_norm_bound_to_eigenvalue` — elementary conversion from a
  norm-bound on `(ker H)ᗮ` to an eigenvalue-level gap.
* `parentHamiltonian_gapped` — uniform spectral gap for MPS parent
  Hamiltonians on injective tensors (deferred).
-/

namespace MPSTensor

open scoped BigOperators InnerProductSpace

variable {d D : ℕ}

/-! ### Ground-space and Hamiltonian transport to `EuclideanSpace` -/

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

/-! ### Norm bound ⟹ eigenvalue-level gap

This is the elementary final step of the martingale method: given the
martingale-derived norm bound `γ ‖v‖ ≤ ‖H v‖` for all `v ⊥ ker H`, convert
it into an eigenvalue-level gap statement. In finite dimensions this is a
one-line consequence of `norm_smul`.

The non-trivial mathematical content — producing the norm bound itself from
the MPS-specific operator inequality `H² ≥ γ H` (which in turn comes from
the Friedrichs-angle estimate on overlapping projector pairs plus a row-sum
bound) — is *not* in this section. It is deferred to the `sorry` in
`parentHamiltonian_gapped`. -/

/--
**Norm bound ⟹ eigenvalue-level gap (elementary conversion step).**

Let `H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι` be a linear endomorphism
of a finite-dimensional complex inner product space, and let `γ > 0`. Suppose

    `γ ‖v‖ ≤ ‖H v‖    for all v ⊥ ker H`.

Then every eigenvalue `μ` of `H` with an eigenvector `v ≠ 0` in `(ker H)ᗮ`
satisfies `γ ≤ ‖μ‖`.

This is the elementary conversion `‖H v‖ = ‖μ‖ * ‖v‖` step — no "martingale"
content is present here. The real work of the martingale method is producing
the hypothesis `hBound`; see `parentHamiltonian_gapped` for where that is
deferred.
-/
theorem spectralGap_norm_bound_to_eigenvalue {ι : Type*} [Fintype ι]
    (H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (γ : ℝ) (_hγ : 0 < γ)
    (hBound : ∀ v : EuclideanSpace ℂ ι,
      v ∈ (LinearMap.ker H)ᗮ → γ * ‖v‖ ≤ ‖H v‖) :
    ∀ (μ : ℂ) (v : EuclideanSpace ℂ ι),
      v ∈ (LinearMap.ker H)ᗮ → v ≠ 0 → H v = μ • v → γ ≤ ‖μ‖ := by
  intro μ v hv hne heq
  have hv_pos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hne
  have h1 : γ * ‖v‖ ≤ ‖H v‖ := hBound v hv
  have h2 : ‖H v‖ = ‖μ‖ * ‖v‖ := by rw [heq, norm_smul]
  rw [h2] at h1
  exact le_of_mul_le_mul_right h1 hv_pos

/-! ### Specialization to the MPS parent Hamiltonian -/

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
`groundSpace_intersection` (PR #265) bounds the Friedrichs angle between
adjacent local ground spaces away from zero, which provides the martingale
operator inequality

    `h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)`

with constants `c_{ij}` depending only on the MPS tensor (not on `N`). At most
`2(L-1)` local terms overlap a given `h_i`, so the row-sum bound
`∑_{j≠i} c_{ij} ≤ 1` holds uniformly in `N`. Combining these via the
spectral theorem yields the norm bound `γ ‖v‖ ≤ ‖H v‖` on `(ker H)ᗮ`, which
is precisely the conclusion below.

The proof is deferred; the operator inequality and its derivation from the
intersection property are the remaining mathematical work. -/
theorem parentHamiltonian_gapped
    (A : MPSTensor d D) (_hA : IsInjective A) (L : ℕ) (_hL : 1 < L) :
    ∃ γ > 0, ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  sorry

end MPSTensor
