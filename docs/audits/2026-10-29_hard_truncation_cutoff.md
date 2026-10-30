# The cutoff for the truncated-side hard-truncation error

This audit concerns TNLean issue #9844 and the literal truncated-side estimate in
ALVV, arXiv:1602.08828v2, Proposition 4.4(1), Section 4.2. The original-side
estimate is not refuted. No source paper is edited.

## Source context checked

- [ALVV v2 PDF](https://arxiv.org/pdf/1602.08828v2), printed pages 14–15:
  the opening paragraph of Section 4.2 says the cutoff is chosen sufficiently
  large relative to the energy width. Definition 4.3 only states `t>0`;
  Proposition 4.4 states both restricted errors without a numerical cutoff
  restriction; Lemma 4.5 explicitly says `t>eta`.
- [AKL v3 PDF](https://arxiv.org/pdf/1406.3898), printed pages 8–9:
  Definition 2.5 and Theorem 2.6 retain a fixed positive clipping threshold;
  the displayed truncated-side estimate has no explicit restriction placing
  the requested low-energy cutoff below the clipped flat sector. Nearby
  Theorem 2.3 states its energy-order restrictions explicitly.
- The sign correction already recorded in QICLean's
  [hard-truncation note](https://sirui-lu.com/QICLean/paper-gaps/alvv16_hard_truncation_windows.pdf)
  is separate. Fixing that sign does not remove the flat-sector obstruction.

## Actual chain and discrepancy

For `K>=2`, the qubit chain has sites `0,...,K+1` and one positive contraction
on each bond. The crossing term is
`(I-P1(0)/4) P0(1)`. The internal terms are `P1(i)` for `1<=i<K` and
`(P1(K)+P1(K+1))/2` on the last bond. The crossing term depends on both its
sites, as does the last internal term. Thus the construction does not depend
on assigning a one-site term a nonminimal boundary support.

`HardTruncationCutoff.bondTerm_supported` and
`bondTerm_positive_contraction` derive the source support and positivity
conditions. `regionalHamiltonian_eq_internal_bond_sum` identifies the actual
regional bond sum on `J={1,...,K+1}`; `hamiltonian_eq_region_add_boundary`
derives the original decomposition. There is no supplied decomposition,
kernel identity, minimum, perturbation bound, or spectral-tail input.

The computational basis vector `(1,0,...,0)` gives regional minimum zero and
ground energy `3/4` for both the original Hamiltonian and its actual regional
clipping at `t=3/2`. `actual_ground_energies` includes the attained normalized
eigenvectors and the positive-semidefinite lower bounds. Uniqueness and the
quarter-unit gap of this particular family are unnecessary for Proposition
4.4 and are not separate formal claims in this submission.

For the unit all-one vector, the original energy is `K` and the clipped
energy is `3/2`. The actual closed spectral projection below
`ground_energy+eta=7/4`, with `eta=1`, therefore fixes this vector. The
restricted discrepancy has norm at least `K-3/2`.
`exists_truncated_low_discrepancy_gt` chooses `K` by the Archimedean property,
so every fixed error constant is exceeded. No huge configuration space is
enumerated, and no numerical exponential estimate is needed.

## Norm and spectral conventions

The operator norm is Mathlib's scoped `Matrix.Norms.L2Operator`. The unit
witness is in `EuclideanSpace`; its norm is not the raw function sup norm.
The norm of a diagonal operator is rewritten using `Matrix.l2_opNorm_diagonal`;
only its scalar diagonal coefficient function then has the usual function
sup norm. The low projection is the actual continuous functional calculus
of the closed indicator `x<=7/4`, which is continuous on this finite spectrum.

## Status and remaining work

The production proof scripts are source-written and uncompiled. The new
Blueprint example and all declaration links remain `notready`. No local
Lean, Lake, elaboration, build, declaration checker, or kernel bypass ran.
Independent source review and exact-head hosted verification are required.

The existing QICLean note is extended in a separate documentation draft;
no duplicate TNLean paper-gap note is introduced. A corrected actual-chain
application at a sufficiently large explicit cutoff remains separate. In
particular, #10404 already derives physical restricted clipping errors with
an explicit separation margin; this example does not invalidate that result
or reimplement its residual estimates. Issue #9844 remains open.
