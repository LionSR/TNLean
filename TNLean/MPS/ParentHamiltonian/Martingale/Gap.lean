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

* `hamiltonian_parentRingInteraction_gapped_of_anticommutator` — conditional uniform spectral
  gap of the Hamiltonian of the parent interaction on the ring under the source anticommutator
  estimate.
-/

open scoped BigOperators InnerProductSpace

namespace MPSTensor

variable {d D : ℕ}

/-! ### Uniform spectral gap for the MPS parent Hamiltonian -/

/--
**Conditional spectral gap from the source anticommutator estimate.**

For an MPS tensor \(A\) and interaction range \(L > 1\), the cyclic-window
anticommutator estimate for the terms \(h_i\) of the parent interaction on the ring
\[
  h_i h_j+h_jh_i\ge
  -\left(1-\frac1{4L}\right)\frac1{2(L-1)}(h_i+h_j)
\]
for overlapping off-diagonal pairs implies a uniform gap \(γ>0\), independent
of the chain length, for the Hamiltonians \(H\) of the parent interaction on the rings of
\(N ≥ 2L\) sites on the orthogonal complement of their kernels.

This is the public gapped theorem matching the martingale condition in
arXiv:2011.12127, Section IV.C, lines 2176-2179. The MPS-specific proof of the
anticommutator estimate remains the open input. -/
theorem hamiltonian_parentRingInteraction_gapped_of_anticommutator
    (A : MPSTensor d D) (L : ℕ) (hL : 1 < L)
    (hAnti : ∀ (N : ℕ) (hLN : 2 * L ≤ N) (i j : Fin N),
      j ∈ Finset.univ.erase i → cyclicWindowsOverlap N L i j →
        ∀ v : EuclideanSpace ℂ (Cfg d N),
          let h (k : Fin N) :=
            Matrix.toEuclideanLin ((parentRingInteraction A (show L ≤ N by omega)).term k);
          - (1 - ((1 : ℝ) / (4 * (L : ℝ)))) * (((2 * (L - 1) : ℕ) : ℝ)⁻¹) *
              ((⟪h i v, v⟫_ℂ).re + (⟪h j v, v⟫_ℂ).re) ≤
            (⟪h i v, h j v⟫_ℂ).re + (⟪h j v, h i v⟫_ℂ).re) :
    ∃ γ > 0, ∀ (N : ℕ) (hLN : 2 * L ≤ N) (v : EuclideanSpace ℂ (Cfg d N)),
      let H := Matrix.toEuclideanLin (parentRingInteraction A (show L ≤ N by omega)).hamiltonian
      v ∈ (LinearMap.ker H)ᗮ → γ * ‖v‖ ≤ ‖H v‖ := by
  obtain ⟨hγ, hgap⟩ :=
    hamiltonian_parentRingInteraction_gap_bound_of_cyclic_window_overlap_anticommutator A L hL
      hAnti
  exact ⟨(1 : ℝ) / (4 * (L : ℝ)), hγ, hgap⟩

end MPSTensor
