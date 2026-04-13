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
6. **Abstract criterion → quadratic form**: the above yields `H² ≥ γ H` as
   operators, which by the spectral theorem gives `γ ‖v‖ ≤ ‖H v‖` for
   `v ⊥ ker H`.

The abstract step `H² ≥ γ H ⟹ gap ≥ γ` is factored into
`spectralGap_of_martingale`, so that the MPS-specific verification reduces to
producing the operator inequality. Both the abstract criterion and its MPS
instantiation are currently left as `sorry`; see the module docstring for
references.

## Main results

* `spectralGap_of_martingale` — abstract martingale criterion packaging.
* `parentHamiltonian_gapped` — uniform spectral gap for MPS parent
  Hamiltonians on injective tensors.
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

/-! ### Abstract martingale criterion

This section isolates the purely operator-theoretic content of the
Kastoryano–Lucia martingale method from the MPS-specific verification.

The final form used below is the "norm-bound" form of the gap statement:
if `γ ‖v‖ ≤ ‖H v‖` holds for all `v` in the orthogonal complement of the
kernel, then `H` is gapped by `γ`. The real mathematical content of the
martingale method is producing this hypothesis from the operator inequality

    `H² ≥ γ H`

(see Kastoryano–Lucia 2018, Theorem 3.1 and Nachtergaele 1996, Lemma 4.1).
The abstract operator inequality in turn follows from a family of projector
bounds on overlapping pairs together with a row-sum bound on the overlap
constants. -/

/--
**Abstract martingale criterion (Kastoryano–Lucia / Nachtergaele).**

Let `H : E →ₗ[ℂ] E` be a linear endomorphism of a finite-dimensional complex
inner product space, and let `γ > 0` be a real number. If `H` admits a
"martingale decomposition" giving rise to the norm-bound

    `γ ‖v‖ ≤ ‖H v‖    for all v ⊥ ker H`,

then `H` is gapped with gap at least `γ`.

This is a packaging statement: it names the conclusion of the full martingale
method so that downstream theorems can cite a single hypothesis. The full
derivation (frustration-free sum of projectors + operator inequality on
overlapping pairs + row-sum bound ⟹ `H² ≥ γ H` ⟹ norm bound) is deferred.

References:
* Kastoryano–Lucia, arXiv:1705.09491, Sections 2–3 (clean modern treatment).
* Nachtergaele, CMP 175 (1996), Lemma 4.1.
* Fannes–Nachtergaele–Werner, CMP 144 (1992) (original gap proof).
-/
theorem spectralGap_of_martingale {ι : Type*} [Fintype ι]
    (H : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) (γ : ℝ) (_hγ : 0 < γ)
    (hBound : ∀ v : EuclideanSpace ℂ ι,
      v ∈ (LinearMap.ker H)ᗮ → γ * ‖v‖ ≤ ‖H v‖) :
    ∀ v : EuclideanSpace ℂ ι,
      v ∈ (LinearMap.ker H)ᗮ → γ * ‖v‖ ≤ ‖H v‖ :=
  hBound

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
`∑_{j≠i} c_{ij} ≤ 1` holds uniformly in `N`. The abstract martingale criterion
`spectralGap_of_martingale` then yields a uniform gap.

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
