/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Reduction

/-!
# Uniform spectral gap for the MPS parent Hamiltonian

**Root-only.** This file contains the final conditional spectral-gap theorems
for the MPS parent Hamiltonian. The overlapping-window principal-angle
estimate remains an explicit hypothesis.

## Main results

* `parentHamiltonianES_gap_bound_of_friedrichs` — the explicit gap bound
  obtained from the overlapping-window norm-compression estimate.
* `parentHamiltonianES_gap_bound_of_overlap_norm_constant` — the corresponding
  positive-gap bound from a strict uniform compression coefficient.
* `parentHamiltonian_gapped` — conditional uniform spectral gap for MPS parent
  Hamiltonians on injective tensors, under the same principal-angle input.
* `parentHamiltonian_gapped_of_overlap_norm_constant` — the corresponding
  uniform spectral gap from a strict uniform compression coefficient.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Uniform spectral gap for the MPS parent Hamiltonian -/

/-- Gap bound from the overlapping cyclic-window principal-angle estimate for the
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

/-- Gap bound from a strict uniform overlapping cyclic-window compression
coefficient for the MPS parent Hamiltonian.

This is the source-faithful form of the remaining martingale input in
arXiv:2011.12127, Section IV.C (the martingale-2 estimate), with an arbitrary
compression constant.  It does not
assert the special coefficient used in
`parentHamiltonianES_gap_bound_of_friedrichs`; instead, it says that any uniform
bound

\(‖p_i p_j v‖ ≤ η ‖p_i v‖\)

with \(η * 2(L-1) < 1\) yields the positive gap constant
\(1 - η * 2(L-1)\).  The comparison between this flexible cyclic-window
hypothesis and the cited FNW--Nachtergaele--Kastoryano principal-angle estimates
is recorded in `docs/paper-gaps/cpgsv21_martingale_overlap.tex`. -/
theorem parentHamiltonianES_gap_bound_of_overlap_norm_constant
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L) {η : ℝ}
    (hηnonneg : 0 ≤ η)
    (hηlt : η * (((2 * (L - 1) : ℕ) : ℝ)) < 1)
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            η * ‖localTermES A L i v‖) :
    0 < 1 - η * (((2 * (L - 1) : ℕ) : ℝ)) ∧
    ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        (1 - η * (((2 * (L - 1) : ℕ) : ℝ))) * ‖v‖ ≤
          ‖parentHamiltonianES A L N v‖ := by
  exact parentHamiltonianES_gap_bound_of_cyclic_window_overlap_norm_bound_of_lt
    A L hL hηnonneg hηlt hOverlapNorm

/--
**Conditional spectral gap for MPS parent Hamiltonians.**

For an injective MPS tensor \(A\) and interaction range \(L > 1\), the
overlapping-window norm-compression estimate implies the existence of a uniform
gap \(γ > 0\) (independent of system size \(N\)). For all \(N ≥ 2L\), every vector
in the orthogonal complement of the ground space satisfies
\(γ ‖v‖ ≤ ‖H_{\mathrm{ES}} v‖\).

The orthogonal complement is computed in the `EuclideanSpace` structure
on `NSiteSpace d N ≃ Cfg d N → ℂ`.

**Proof strategy (Kastoryano–Lucia 2018 / Nachtergaele 1996).** The parent
Hamiltonian \(H_N = ∑ᵢ hᵢ\) is a frustration-free sum of local orthogonal
projectors (`parentHamiltonian_frustrationFree`). The intersection property
`groundSpace_intersection` gives the local relation

    \(\ker h_{\mathrm{left}} \cap \ker h_{\mathrm{right}} \subseteq \ker h\)

where \(h_{\mathrm{left}}\) and \(h_{\mathrm{right}}\) are the two overlapping
length-\(L\) projectors and \(h\) is the length-\(L+1\) projector. The remaining
principal-angle estimate
supplies the martingale operator inequality

    \(h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)\)

with row-summable coefficients. At most \(2(L-1)\) local terms overlap a given
length-\(L\) cyclic window, so the chosen coefficients have row sum at most one.
Combined with \(h_i^2 = h_i\), this yields the quadratic-form inequality
\(H² ≥ γ H\), which feeds into the abstract lemma
`FrustrationFree.spectralGap_of_martingale` to produce the norm bound
\(γ ‖v‖ ≤ ‖H v‖\) on \((\ker H)^\perp\). The `LinearMap.IsPositive` hypothesis required
by `FrustrationFree.spectralGap_of_martingale` is automatic here because
\(H_N = ∑ᵢ hᵢ\) is a sum of orthogonal projectors.

The proof below invokes
`parentHamiltonianES_gap_bound_of_friedrichs`, which combines the already
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

/--
**Conditional spectral gap from a strict overlapping-window compression
coefficient.**

For an MPS tensor \(A\) and interaction range \(L > 1\), any uniform
overlapping cyclic-window estimate
\(‖p_i p_j v‖ ≤ η ‖p_i v‖\) with \(0 ≤ η\) and \(η * 2(L-1) < 1\) gives a uniform
positive lower bound on the parent Hamiltonian, independent of the chain length.

This is the version of `parentHamiltonian_gapped` with an arbitrary compression
constant.  It is the appropriate target if the principal-angle estimates cited
in arXiv:2011.12127, Section IV.C, first produce an unspecified positive
compression constant rather than the explicit coefficient
\((1 - 1/(4L)) / (2(L-1))\). -/
theorem parentHamiltonian_gapped_of_overlap_norm_constant
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L) {η : ℝ}
    (hηnonneg : 0 ≤ η)
    (hηlt : η * (((2 * (L - 1) : ℕ) : ℝ)) < 1)
    (hOverlapNorm : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          ‖localTermES A L i (localTermES A L j v)‖ ≤
            η * ‖localTermES A L i v‖) :
    ∃ γ > 0, ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  obtain ⟨hγ, hgap⟩ :=
    parentHamiltonianES_gap_bound_of_overlap_norm_constant A L hL hηnonneg
      hηlt hOverlapNorm
  exact ⟨1 - η * (((2 * (L - 1) : ℕ) : ℝ)), hγ, hgap⟩

end MPSTensor
