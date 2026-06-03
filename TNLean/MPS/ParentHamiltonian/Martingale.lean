/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Martingale.AbstractCriterion
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.ParentHamiltonian.Martingale.Reduction

/-!
# Martingale-method spectral-gap framework for parent Hamiltonians

This module collects the proof-complete martingale-method infrastructure for the
MPS parent-Hamiltonian spectral gap and is imported by the project root.  The
Friedrichs-angle estimate needed to close `parentHamiltonian_gapped` is the
remaining analytic step, so `Martingale.Gap` stays separate until that estimate
is proved.

This file collects the three proof-complete infrastructure submodules:

* `Martingale.AbstractCriterion` — abstract martingale criterion
  `FrustrationFree.spectralGap_of_martingale` (quadratic form ⟹ norm bound);
* `Martingale.Transport` — Euclidean local projectors, ground-space /
  Hamiltonian transport, positivity, commutation, and kernel identification;
* `Martingale.Reduction` — martingale quadratic-form reduction chain from
  ordered cross-term bounds down to concrete cyclic-window Friedrichs.

The final spectral-gap pair `parentHamiltonianES_gap_bound_of_friedrichs` and
`parentHamiltonian_gapped` remains in `Martingale.Gap`; it is not imported here
until the Friedrichs-angle estimate is proved.

## Proof route

1. **Frustration-freeness** (`parentHamiltonian_frustrationFree`): every local
   term annihilates the MPV ground state.
2. **Local projector structure** (`parentInteraction`/`localTerm`): each local
   term is an orthogonal projector on its `L`-site window.
3. **Intersection property** (`groundSpace_intersection`): for an injective
   MPS tensor, the kernel of the sum of two overlapping local terms equals
   the intersection of their kernels.
4. **Martingale operator bound**: the intersection property gives a positive
   Friedrichs angle between adjacent local ground spaces, which is the
   quantitative content of

        `h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)`

   with constants `c_{ij}` depending only on the MPS tensor, not on `N`.
5. **Row-sum bound** `∑_{j ≠ i} c_{ij} ≤ 1`: at most `2(L-1)` local terms
   overlap a given local term.
6. **Quadratic form ⟹ norm bound**: combining the above with `h_i^2 = h_i`
   yields `H² ≥ γ H` as a quadratic form, which by the spectral theorem
   gives `γ ‖v‖ ≤ ‖H v‖` for `v ⊥ ker H`.
-/
