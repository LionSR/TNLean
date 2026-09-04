/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.AbstractCriterion
import TNLean.MPS.ParentHamiltonian.Martingale.AdjacentLocalTerms
import TNLean.MPS.ParentHamiltonian.Martingale.AnalyticBounds
import TNLean.MPS.ParentHamiltonian.Martingale.BlockedGap
import TNLean.MPS.ParentHamiltonian.Martingale.BlockedOriginalComparison
import TNLean.MPS.ParentHamiltonian.Martingale.C3Threshold
import TNLean.MPS.ParentHamiltonian.Martingale.CyclicWindowOpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.DifferenceProjections
import TNLean.MPS.ParentHamiltonian.Martingale.EmbeddedC2
import TNLean.MPS.ParentHamiltonian.Martingale.FiberwiseQuadraticFormGap
import TNLean.MPS.ParentHamiltonian.Martingale.FiniteRangeKnabeGap
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbient
import TNLean.MPS.ParentHamiltonian.Martingale.FixedAmbientMartingaleBound
import TNLean.MPS.ParentHamiltonian.Martingale.Gap
import TNLean.MPS.ParentHamiltonian.Martingale.MovingWindowCount
import TNLean.MPS.ParentHamiltonian.Martingale.NachtergaeleFullRangeEstimate
import TNLean.MPS.ParentHamiltonian.Martingale.OpenChain
import TNLean.MPS.ParentHamiltonian.Martingale.OpenHamiltonian
import TNLean.MPS.ParentHamiltonian.Martingale.OpenParentGap
import TNLean.MPS.ParentHamiltonian.Martingale.OverlapReduction
import TNLean.MPS.ParentHamiltonian.Martingale.ProjectionCancellation
import TNLean.MPS.ParentHamiltonian.Martingale.QuadraticFormGap
import TNLean.MPS.ParentHamiltonian.Martingale.Reduction
import TNLean.MPS.ParentHamiltonian.Martingale.SpectatorTransport
import TNLean.MPS.ParentHamiltonian.Martingale.Transport

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
MPS-specific anticommutator estimate remains a separate hypothesis. Stronger
all-vector norm-compression estimates for the excitation projections are also
recorded as conditional sufficient hypotheses; they are not the source
principal-angle estimate for the local ground spaces.

The twenty-five components are:

* `Martingale.AbstractCriterion` — abstract martingale criterion
  `FrustrationFree.spectralGap_of_martingale_of_finiteDimensional`
  (quadratic form implies norm bound);
* `Martingale.QuadraticFormGap` — a positive operator's norm gap implies the
  global quadratic-form inequality needed for a finite-range Knabe estimate;
* `Martingale.FiberwiseQuadraticFormGap` — the same inequality persists when
  the operator acts independently over a finite spectator coordinate;
* `Martingale.FiniteRangeKnabeGap` — the open-window gap implies a uniform
  periodic parent-Hamiltonian gap with the finite-range Knabe coefficient;
* `Martingale.AnalyticBounds` — the weighted inner-product and C3
  projection-composition inequalities from Nachtergaele's summation;
* `Martingale.DifferenceProjections` — Nachtergaele's mutually orthogonal
  martingale differences, telescoping resolution, and norm-square decomposition;
* `Martingale.ProjectionCancellation` — outside-window cancellation and the
  finite interval reduction between equations \(Enpsi\) and \(Enpsi2\);
* `Martingale.FixedAmbient` — fixed-volume prefix and interval ground projections,
  physical outside-window commutation, and the resulting interval reduction;
* `Martingale.SpectatorTransport` — norm-preserving right-spectator sums and
  conjugacies for the fixed-volume prefix and interval projectors;
* `Martingale.FixedAmbientMartingaleBound` — the fixed-volume boundary cases
  and literal condition C3 on every active index;
* `Martingale.Transport` — Euclidean local projectors, ground-space and
  Hamiltonian transport, positivity, commutation, and kernel identification;
* `Martingale.AdjacentLocalTerms` — individual three-site kernels and the
  identification of complementary open-chain projections with the adjacent
  range-two local terms;
* `Martingale.OpenChain` — open-chain ground-space projectors, their intersection,
  and the projector-defect reduction to an anticommutator estimate;
* `Martingale.OpenHamiltonian` — the nonwrapping finite-volume Hamiltonian and its
  kernel identification with the open MPS boundary-condition space;
* `Martingale.CyclicWindowOpenHamiltonian` — cyclic-site coordinates, finite-range
  disjointness, and the identification of Knabe blocks with fiberwise open Hamiltonians;
* `Martingale.EmbeddedC2` — the unique fixed-window suffix interaction and
  condition C2 with constant one;
* `Martingale.C3Threshold` — a uniform input-site overlap length satisfying the
  open-chain C3 defect threshold and its anticommutator consequence;
* `Martingale.BlockedGap` — transport of that threshold to three blocked sites
  and the explicit range-two blocked parent-Hamiltonian gap;
* `Martingale.BlockedOriginalComparison` — exact conjugacy of the blocked
  parent interaction and of the blocked range-two local terms with their
  original range-\(2p\) counterparts at block-aligned starts;
* `Martingale.MovingWindowCount` — reversal and counting of the finite moving-window
  sums in Nachtergaele's martingale estimate;
* `Martingale.NachtergaeleFullRangeEstimate` — the source's printed martingale-difference
  summation with the exact C1--C3 energy coefficient and its norm-gap form;
* `Martingale.OpenParentGap` — the physical nonwrapping open MPS specialization,
  with \(d_{l+1}=\gamma_{l+1}=1\) and the same \(\epsilon_l\) as condition C3;
* `Martingale.OverlapReduction` — reduction from overlapping-window commutation
  to all-pairs commutation using locality for disjoint windows;
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
   The cited principal-angle estimates concern the reduced local ground
   spaces. Converting them to this anticommutator bound remains the source-facing
   quantitative input; the all-vector excitation-projection norm bounds recorded
   in this development are only stronger conditional sufficient hypotheses.
5. **Row-sum bound** \(\sum_{j\ne i} c_{ij}\le 1\): at most \(2(L-1)\) local terms
   overlap a given length-\(L\) cyclic window under the convention used here.
6. **Quadratic form to norm bound**: combining these estimates with \(h_i^2=h_i\)
   yields \(H^2\ge\gamma H\) as a quadratic form, which by the spectral theorem
   gives \(\gamma\|v\|\le\|Hv\|\) for \(v \perp \ker H\).
-/
