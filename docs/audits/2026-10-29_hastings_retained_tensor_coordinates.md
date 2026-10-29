# Tensor coordinates for the retained Hastings hierarchy

This review distinguishes the tensor-coordinate construction in Hastings' 2006
paper from quantitative bond bounds which the paper explicitly leaves open.
The statements below concern the source argument and the existing mathematical APIs.

## Source passages

The source is Hastings, *Solving gapped Hamiltonians locally*,
[arXiv:cond-mat/0508554v3](https://arxiv.org/abs/cond-mat/0508554v3),
`References/cond-mat_0508554/proj3new.tex`, SHA256
`0c87b269f4b7d351462dc9c51b1a4460f6029f0dd2598c1e65f944aaf35f79cd`.

At lines 104–109 the introduction explicitly declines to bound the number of
states required by its matrix-product construction and explains that the
construction assumes knowledge of certain ground-state properties. Accordingly,
a polynomial bound for all intermediate virtual spaces is not an unproved
claim of this paper. Such a bound would be an additional theorem.

The tensor-coordinate argument has the following concrete steps.

| Source lines | Mathematical step |
|---|---|
| 511–536 | A state on a larger block is expanded in a basis of a smaller block and a local physical basis, with coefficients A. Contracting the repeated coefficients gives its amplitudes. |
| 609–628 | Physical sites are grouped into neighbouring supersites. The local filters are assigned to pairs. On an exactly sized first block of 2ℓ sites the physical dimension is at most q^(2ℓ). |
| 630–643 | Choose a complete basis at the leaves, then choose eigenvectors in the first retained spectral windows as bases for the retained pair spaces. |
| 669–685 | Each next compressed operator is diagonalized inside the tensor product of the two child retained spaces. Its retained eigenvectors therefore have coefficients in the tensor products of the two child bases. |
| 705–730 | The error is controlled through the levels; the final retained orthonormal family has cardinality at most twice the original ground-space dimension. |
| 745–756 | The method is extended by grouping coordinate slices, or by using 2^d children per grouping. No new intermediate dimension estimate is stated. |

The local residual assumption is explicit at lines 493–507, before the
construction. In the unique-ground corollary it has now been derived from the
original gap. In the general degenerate case its basis-selection question
remains separate from the tensor-coordinate construction reviewed here.

## What the current result proves

`IsRetainedHierarchy` proves that a final retained vector is retained by every
descendant projection. The actual projections, support regions, pair assignment,
adaptive windows, and periodic closing window are constructed. The new
unique-ground corollary also proves the final cardinality bound two.

These assertions do not themselves exhibit a coefficient tensor at every vertex
or a recursive amplitude contraction. In particular, a final global rank bound
does not bound a local Schmidt rank: the projection onto one maximally entangled
vector has rank one while the vector can have any prescribed Schmidt rank D.
No inference from the final bound two to intermediate bond bounds is justified.

There is also an important coordinate distinction. A hierarchy projection
supported on a block S is a local projection tensored with the identity outside
S. Its full-system rank includes the entire exterior multiplicity. A basis of
that global range is not the local block basis used in the source, and tensoring
two such global bases would duplicate the exterior Hilbert space. The actual
local projection must first be extracted from the support statement.

## Existing APIs

The reviewed provider was TNLean
`7f87bdc8f1b2354be4950ad515dedda7ee9bec96` with QICLean package
`ec3434f7d6fbdfc5318dc55934feb9532e239b81`. The following declarations were
read in their actual sources.

| Task | Existing declarations |
|---|---|
| Convert physical algebra support to coordinate support | `QuantumCircuit.isSupportedOn_of_mem_supportedOperators`, in `TNLean/Circuit/EntropySupport.lean` |
| Extract the local matrix | `Entropy.IsSupportedOn.exists_localLift`, in `QICLean/Entropy/LocalLift.lean`; the supplied configuration can be chosen once when q>0 |
| Preserve and reflect local algebraic identities | `Entropy.localLift_mul`, `localLift_one`, `localLift_conjTranspose`; `Entropy.localLift_injective`, in `QICLean/Entropy/FilterPower.lean` |
| Split a parent region into its two actual children | `Entropy.regionUnionEquiv`, `Entropy.localLift_union_kronecker`, in `QICLean/Entropy/RegionUnion.lean` |
| Choose coordinates for an actual projection | `IsStarProjection.exists_matrix_range_isometry`, in `QICLean/Algebra/ProjectionRangeIsometry.lean`; includes zero projection and empty ambient coordinate type |
| Tensor two isometries | `Matrix.IsIsometry.kronecker`, in `QICLean/Algebra/MatrixIsometryKronecker.lean` |
| Identify the chosen coordinate dimension | `Matrix.IsIsometry.rank_eq_card`, `Matrix.IsIsometry.card_le`, in `QICLean/Algebra/MatrixUnitaryBetween.lean`; `Matrix.rank_self_mul_conjTranspose`, in Mathlib's `LinearAlgebra/Matrix/Rank.lean` |
| Expand a rectangular matrix product into coefficients | `Matrix.mul_apply`, `Matrix.mulVec_mulVec`, `Matrix.kroneckerMap_apply`; standard matrix identities suffice |
| Existing fixed-dimension tree contraction | `MPSPreparation.IsometryTree.matrix`, `matrix_fork_apply`, `isIsometry_matrix`, in `TNLean/MPS/Preparation/IsometryTree.lean` |
| Existing explicit tree amplitude sums | `MPSTensor.treeAmp`, `binaryTreeMatrix_apply_unpair`, in `TNLean/MPS/Preparation/TreeAmplitude.lean` |

The existing `IsometryTree` has one fixed virtual dimension χ at all vertices,
positive physical leaf lengths, and a fixed leaf-size bound. The current
hierarchy has varying retained ranks and padded empty blocks. It therefore
cannot simply be inserted into that type without an additional construction.
The exact PEPS construction in `PEPS/Approximation/ExactTreeRepresentation.lean`
carries the whole physical configuration on each active edge; it is a different
representation and does not supply the retained-basis expansion of Section III.

## The next bounded construction

The next generic result belongs in QICLean, separately from the physical
Hamiltonian theorem. Let P be a star projection on the finite coordinate space
α×β, and Q and R star projections on α and β. Assume

    (Q ⊗ R)P = P.

Choose actual range isometries U_P,U_Q,U_R using the existing projection
coordinate theorem, so U_P U_P* = P and likewise for Q,R. Set

    A = U_Q ⊗ U_R,       W = A* U_P.

Then A*A=I and AA*=Q⊗R. The range inclusion gives AA*U_P=U_P, because
P U_P=U_P. Therefore

    W*W = U_P* AA* U_P = I,       U_P = A W.

This constructs the parent coefficient tensor rather than assuming one.
If the chosen coordinate dimensions are r_P,r_Q,r_R, then

    r_P = rank P,       r_Q = rank Q,       r_R = rank R,
    r_P ≤ r_Q r_R.

The dimension inequality follows from the constructed isometry W. Zero ranks
must be allowed. If either child rank is zero, the inclusion forces P=0 and
the parent coordinate type is empty. No positive-rank or nonempty-coordinate
hypothesis is needed for this generic result.

This result is an auxiliary coordinate theorem with explicit projection
hypotheses. It must not be labelled a completed physical tensor representation
until the actual hierarchy projections have been substituted and the following
steps have been proved.

1. Extract the local star projection at each actual hierarchy block from its
   supported full-system projection. Reflect self-adjointness, idempotence and
   parent inclusion using the injective local lift.
2. Use the actual disjoint union of the two child blocks, including empty padded
   blocks, to identify the parent physical coordinates with a product. The
   source's parent inclusion then gives the hypothesis of the generic result.
3. Choose the isometric coordinates simultaneously at the finitely many nodes,
   define the variable-dimension coefficient tensors W, and prove recursively
   that their contraction equals each local inclusion map. At the root, use the
   coordinate vector of the retained state. The additional closing window is a
   final unary isometry into the binary-tree root, not a missing pair in the tree.

The elementary local bounds available along this route are

    r_v ≤ q^|S_v|,       r_parent ≤ r_left r_right.

For the rounded physical geometry a leaf has fewer than 4ℓ sites (or the chain
is a single shorter leaf); hence its dimension is at most q^(4ℓ) when q≥1.
These elementary bounds can grow exponentially with a large block. They are
consistent with the source's explicit disclaimer and are not polynomial bond
bounds. A stronger intermediate rank theorem would require new mathematical
input beyond the source and beyond the final global rank estimate.

