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

The MPS parent-Hamiltonian spectral gap is reduced to the anticommutator
martingale condition stated in arXiv:2011.12127, Section IV.C. For the
frustration-free sum of orthogonal projectors \(H=\sum_i h_i\), the required
estimate for overlapping length-\(L\) windows has the form
\(h_i h_j+h_j h_i \ge -c_{ij}(1-\gamma)(h_i+h_j)\) with row sums
\(\sum_{j\ne i} c_{ij}\le 1\), since at most \(2(L-1)\) local terms overlap a
given window. Together with \(h_i^2=h_i\) this gives the quadratic-form
inequality \(H^2\ge \gamma H\), and the spectral theorem turns that into the
norm bound \(\gamma\|v\|\le \|Hv\|\) on \((\ker H)^\perp\). The
MPS-specific anticommutator estimate remains a separate hypothesis. A
norm-compression estimate from principal angles is also recorded as a sufficient
stronger route.

The four components are:

* `Martingale.AbstractCriterion` — abstract martingale criterion
  `FrustrationFree.spectralGap_of_martingale` (quadratic form implies norm bound);
* `Martingale.Transport` — Euclidean local projectors, ground-space and
  Hamiltonian transport, positivity, commutation, and kernel identification;
* `Martingale.Reduction` — martingale quadratic-form reductions from ordered
  cross-term and anticommutator bounds to concrete cyclic-window estimates;
* `Martingale.Gap` — conditional gap theorems from the overlapping cyclic-window
  anticommutator estimate and from sufficient norm-compression estimates.

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
   anticommutator estimate

        \(h_i h_j+h_j h_i\ge -c_{ij}(1-\gamma)(h_i+h_j)\)

   with coefficients whose rows are summable uniformly in the chain length.
   Principal-angle estimates may supply this bound through a norm-compression
   inequality for the corresponding excitation projections.
5. **Row-sum bound** \(\sum_{j\ne i} c_{ij}\le 1\): at most \(2(L-1)\) local terms
   overlap a given length-\(L\) cyclic window under the convention used here.
6. **Quadratic form to norm bound**: combining these estimates with \(h_i^2=h_i\)
   yields \(H^2\ge\gamma H\) as a quadratic form, which by the spectral theorem
   gives \(\gamma\|v\|\le\|Hv\|\) for \(v \perp \ker H\).
-/
