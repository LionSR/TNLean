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

`AdjacentSupportGeneration.lean` now derives the actual AARReven equality.
Faithful embedding transports the two actual finite factor presentations to
their quasi-local copies. The existing commuting-factor theorem is generalized
from an ambient matrix algebra to an arbitrary nontrivial complex star-algebra;
its simplicity proof is unchanged. This gives a genuine full-matrix presentation
of the actual adjacent join. The pair-image inclusion is transported between
full matrix algebras. The already-derived scalar relative commutant invokes
the pinned QICLean surjectivity theorem, so no strictness or size equality is
assumed. All public inputs remain exactly the homogeneous nearest-neighbour
automorphism domain of the source argument.

The first size identity is also derived for the same coherent positive
site-indexed family: r(2x)r(2x+1)=d². The actual pair-image equivalence
composes with the actual support-product presentation, and the accepted
matrix-algebra equivalence theorem equates their matrix sizes. No equality
of vector-space dimensions is mislabeled as an equality of matrix sizes.

The distinct AARRodd argument is now also source-written. Both supports
embed into the same physical pair. An observable on that pair which commutes
with them commutes with every other support factor by disjoint locality.
The global support commutant theorem makes it scalar. Transport to the
actual full-matrix presentations invokes the same accepted finite relative-
commutant surjectivity theorem, now with the physical pair as target. This
derives the second adjacent-generation equality rather than assuming it.
The second matrix-size equality follows from its matrix algebra equivalence.
The final existence theorem records both identities for the same coherent
positive site-indexed size family.

The mathematical conclusions requested by #7122 are source-written with
homogeneous nearest-neighbour automorphism inputs only. Hosted Lean
verification and integration remain outstanding; the issue stays open.
No index construction or MPU correspondence is claimed.

Validation: import-generation, source/prose/whitespace and integrity checks
passed. No local Lean invocation, build or checkdecls was run, as requested.
All new Blueprint entries remain notready, with hosted verification pending.
