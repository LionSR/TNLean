# Scalar centers and positive presentations of actual QCA support algebras

Issue #7122, parent #7038. Main audited:
`efa3070d3060aa49df30530b9eda1b6484c668f2`.

The source first proves scalar centers before either adjacent-generation
identity. GNVW arXiv:0910.3675v2, Section 7.2, source lines 1276–1282,
uses pairwise commutation, quasi-local generation and the scalar global
center. This order was checked against the primary text at
https://arxiv.org/html/0910.3675v2#S7.SS2.

`SupportAlgebraFactors.lean` derives scalar center for every member of the
actual site-indexed embedded family using the existing pairwise commutation,
norm-closed generation commutant consequence and scalar-center theorem.
Faithfulness of each canonical finite-region embedding then transports
centrality to the actual finite even/left and odd/right support algebras.
No commutation or generation conclusion is supplied as a new hypothesis.

The positive full-matrix presentations consume the existing accepted
QICLean theorem `StarSubalgebra.exists_starAlgEquiv_matrix_of_isCentral`,
at the unchanged pinned commit `acda92aa70e69b37507e422bceb5414036859fe6`.
The finite classification is not duplicated. Simultaneous choice in the two
parity families gives a coherent positive integer matrix size r(y), with
explicit star-algebra equivalences in the correct even/left, odd/right order.
The matrix size is not replaced by the vector-space dimension.

The only QCA inputs are a star-automorphism of the homogeneous chain and its
nearest-neighbour propagation. No translation covariance, bundled QCA
predicate, factor presentation, scalar-center premise or global spatial
block form is assumed. The existing homogeneous-chain paper-gap note and
the QICLean-owned full-matrix classification note are cited; neither is
silently treated as the unrestricted site-dependent or direct-sum theorem.

`SupportAlgebraGeneration.lean` also exposes the actual intermediate
even-pair-image commutant theorem needed for the first strict-inclusion
argument. It assumes only commutation with the automorphic images of the
even-pair algebras, not commutation with each separate support factor.
Even-pair algebraic generation, density, continuity and surjectivity derive
commutation with the entire quasi-local algebra. Propagation is not needed
for this intermediate lemma.

The pair-image containment now lands in its own adjacent support join,
not merely in the join of the entire family. Distinct such joins commute.
An element in one join commuting with its actual image-pair algebra therefore
commutes with every image pair, hence is scalar by the derived intermediate
commutant theorem. This proves the actual relative-commutant assertion
required in the first strict-inclusion argument, with no such assertion
assumed as a premise.

Remaining in #7122: AARReven, AARRodd and both homogeneous size identities.
The first equality still needs the finite full-matrix relative-commutant
separation theorem transported through the now-derived matrix presentations.
The second has its own ambient-pair strict-inclusion argument. Neither
adjacent-generation equality is claimed by the present source.

Validation: import-generation, source/prose/whitespace and integrity checks
passed. No local Lean invocation, build or checkdecls was run, as requested.
All new Blueprint entries remain notready, with hosted verification pending.
