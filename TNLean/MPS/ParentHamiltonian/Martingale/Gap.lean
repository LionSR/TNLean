/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Reduction

/-!
# Uniform spectral gap for the MPS parent Hamiltonian

**Root-only.** This file contains the final conditional spectral-gap theorems
for the MPS parent Hamiltonian. The overlapping-window Friedrichs-angle
estimate remains an explicit hypothesis.

## Main results

* `parentHamiltonianES_gap_bound_of_friedrichs` — the explicit gap bound
  obtained from the overlapping-window norm-compression estimate.
* `parentHamiltonian_gapped` — conditional uniform spectral gap for MPS parent
  Hamiltonians on injective tensors, under the same Friedrichs input.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Uniform spectral gap for the MPS parent Hamiltonian -/

/-- Gap bound from the overlapping cyclic-window Friedrichs estimate for the
MPS parent Hamiltonian.

The hypothesis is the precise norm-compression estimate for overlapping
cyclic-window local projections. The finite row-counting geometry, non-overlap
positivity, projection-geometry comparison, and spectral-theorem step are already
formalized in `Martingale.Reduction`. The comparison between this explicit
cyclic-window hypothesis and the martingale paragraph in arXiv:2011.12127,
Section IV.C, is recorded in `docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem parentHamiltonianES_gap_bound_of_friedrichs
    (A : MPSTensor d D) (_hA : IsInjective A) (L : ℕ) (hL : 1 < L)
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            ((1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹)) * ‖localTermES A L i v‖) :
    0 < (1 : ℝ) / (4 * (L : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        ((1 : ℝ) / (4 * (L : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  exact parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound A L hL
    hOverlapNorm

/--
**Conditional spectral gap for MPS parent Hamiltonians.**

For an injective MPS tensor `A` and interaction range `L > 1`, the
overlapping-window norm-compression estimate implies the existence of a uniform
gap `γ > 0` (independent of system size `N`). For all `N ≥ 2L`, every vector
in the orthogonal complement of the ground space satisfies
`γ * ‖v‖ ≤ ‖H_ES v‖`.

The orthogonal complement is computed in the `EuclideanSpace` structure
on `NSiteSpace d N ≃ Cfg d N → ℂ`.

**Proof strategy (Kastoryano–Lucia 2018 / Nachtergaele 1996).** The parent
Hamiltonian `H_N = ∑ᵢ hᵢ` is a frustration-free sum of local orthogonal
projectors (`parentHamiltonian_frustrationFree`). The intersection property
`groundSpace_intersection` gives the local relation

    `ker h_left ∩ ker h_right ⊆ ker h`

where `h_left` and `h_right` are the two overlapping length-`L` projectors and
`h` is the length-`L+1` projector. The remaining Friedrichs-angle estimate
supplies the martingale operator inequality

    `h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)`

with row-summable coefficients. At most `2(L-1)` local terms overlap a given
length-`L` cyclic window, so the chosen coefficients have row sum at most one.
Combined with `h_i^2 = h_i`, this yields the quadratic-form inequality
`H² ≥ γ H`, which feeds into the abstract lemma
`FrustrationFree.spectralGap_of_martingale` to produce the norm bound
`γ ‖v‖ ≤ ‖H v‖` on `(ker H)ᗮ`. The `LinearMap.IsPositive` hypothesis required
by `FrustrationFree.spectralGap_of_martingale` is automatic here because
`H_N = ∑ᵢ hᵢ` is a sum of orthogonal projectors.

The proof below invokes
`parentHamiltonianES_gap_bound_of_friedrichs`, which packages the already
formalized martingale reductions after the overlapping-window estimate is given. -/
theorem parentHamiltonian_gapped
    (A : MPSTensor d D) (hA : IsInjective A) (L : ℕ) (hL : 1 < L)
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            ((1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹)) * ‖localTermES A L i v‖) :
    ∃ γ > 0, ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  obtain ⟨hγ, hgap⟩ := parentHamiltonianES_gap_bound_of_friedrichs A hA L hL
    hOverlapNorm
  exact ⟨(1 : ℝ) / (4 * (L : ℝ)), hγ, hgap⟩

end MPSTensor
