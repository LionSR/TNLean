/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Reduction

/-!
# Uniform spectral gap for the MPS parent Hamiltonian

**Root-only.** This file contains the conditional spectral-gap theorem for the
MPS parent Hamiltonian. The source anticommutator estimate for overlapping
cyclic windows remains an explicit hypothesis.

## Main results

* `parentHamiltonian_gapped_of_anticommutator` — conditional uniform spectral
  gap under the source anticommutator estimate.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Uniform spectral gap for the MPS parent Hamiltonian -/

/--
**Conditional spectral gap from the source anticommutator estimate.**

For an MPS tensor \(A\) and interaction range \(L > 1\), the cyclic-window
anticommutator estimate
\[
  h_i h_j+h_jh_i\ge
  -\left(1-\frac1{4L}\right)\frac1{2(L-1)}(h_i+h_j)
\]
for overlapping off-diagonal pairs implies a uniform gap \(γ>0\), independent
of the chain length.

This is the public gapped theorem matching the martingale condition in
arXiv:2011.12127, Section IV.C, lines 2176-2179. The MPS-specific proof of the
anticommutator estimate remains the open input. -/
theorem parentHamiltonian_gapped_of_anticommutator
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hAnti : ∀ (N : ℕ) (_hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) *
              (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
              ((⟪localTermES A L i v, v⟫_ℂ).re +
                (⟪localTermES A L j v, v⟫_ℂ).re) ≤
            (⟪localTermES A L i v, localTermES A L j v⟫_ℂ).re +
              (⟪localTermES A L j v, localTermES A L i v⟫_ℂ).re) :
    ∃ γ > 0, ∀ (N : ℕ) (_hLN : 2 * L ≤ N)
      (v : EuclideanSpace ℂ (Cfg d N)),
      v ∈ (parentHamiltonianGroundSpaceES A L N)ᗮ →
        γ * ‖v‖ ≤ ‖parentHamiltonianES A L N v‖ := by
  obtain ⟨hγ, hgap⟩ :=
    parentHamiltonianES_gap_bound_of_cyclic_window_overlap_anticommutator A L hL hAnti
  exact ⟨(1 : ℝ) / (4 * (L : ℝ)), hγ, hgap⟩

end MPSTensor
