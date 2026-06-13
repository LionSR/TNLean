/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.Martingale.AbstractCriterion
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.ParentHamiltonian.Martingale.Reduction
import TNLean.MPS.ParentHamiltonian.Martingale.Gap

/-!
# Martingale estimate for parent Hamiltonians

The MPS parent-Hamiltonian spectral gap is reduced to a uniform Friedrichs-angle
bound on adjacent local ground spaces. For the frustration-free sum of orthogonal
projectors \(H=\sum_i h_i\), the principal-angle estimate on overlapping length-\(L\)
windows yields the anticommutator inequality
\(h_i h_j+h_j h_i \ge -c_{ij}(1-\gamma)(h_i+h_j)\) with row sums
\(\sum_{j\ne i} c_{ij}\le 1\), since at most \(2(L-1)\) local terms overlap a
given window. Together with \(h_i^2=h_i\) this gives the quadratic-form
inequality \(H^2\ge \gamma H\), and the spectral theorem turns that into the
norm bound \(\gamma\|v\|\le \|Hv\|\) on \((\ker H)^\perp\). The
Friedrichs-angle estimate itself remains a separate hypothesis.

The four components are:

* `Martingale.AbstractCriterion` — abstract martingale criterion
  `FrustrationFree.spectralGap_of_martingale` (quadratic form implies norm bound);
* `Martingale.Transport` — Euclidean local projectors, ground-space and
  Hamiltonian transport, positivity, commutation, and kernel identification;
* `Martingale.Reduction` — martingale quadratic-form reduction chain from
  ordered cross-term bounds down to concrete cyclic-window Friedrichs;
* `Martingale.Gap` — conditional gap theorems from the overlapping
  cyclic-window estimate.

## Argument

1. **Frustration-freeness** (`parentHamiltonian_frustrationFree`): every local
   term annihilates the periodic MPS vector \(V^{(N)}(A)\).
2. **Local projector structure** (`parentInteraction`/`localTerm`): each local
   term is an orthogonal projector on its \(L\)-site window.
3. **Intersection property** (`groundSpace_intersection`): for an injective
   MPS tensor, the kernel of the sum of two overlapping local terms equals
   the intersection of their kernels.
4. **Martingale operator bound**: the intersection property identifies the
   kernels of overlapping local terms. The remaining quantitative input is the
   Friedrichs-angle estimate, equivalently the anticommutator bound

        \(h_i h_j + h_j h_i ≥ - c_{ij} (1 - γ) (h_i + h_j)\)

   with coefficients whose rows are summable uniformly in the chain length.
5. **Row-sum bound** \(\sum_{j\ne i} c_{ij}\le 1\): at most \(2(L-1)\) local terms
   overlap a given length-\(L\) cyclic window under the convention used here.
6. **Quadratic form ⟹ norm bound**: combining these estimates with \(h_i^2 = h_i\)
   yields \(H² ≥ γ H\) as a quadratic form, which by the spectral theorem
   gives \(γ ‖v‖ ≤ ‖H v‖\) for \(v \perp \ker H\).
-/
