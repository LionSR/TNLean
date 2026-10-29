# Real skew-orthogonal normal-form work

Source use site: CPSV17, arXiv:1703.09188,
`Papers/1703.09188/paper_v2.tex:1129–1140`, proof of `corconj`.
Tracker #7572; remaining mathematical task #7581.
Baseline: main `152f3c81984a0d25599471bf700ecc967e13777f`.

## Existing results and scouting

`TNLean/Algebra/UnitaryCongruence.lean` already proves
`Matrix.exists_skew_unitary_congruence`: a complex skew unitary is congruent,
by a symmetric unitary, to a real skew unitary. This is the completed #7580
ingredient, not the missing real orthogonal block form. QICLean's
`SkewSymmetricMatrix` supplies the even-dimension obstruction.

The pinned Mathlib has `LinearIsometry`, orthonormal families and bases,
`Submodule.orthogonalDecomposition`, `finrank_add_finrank_orthogonal`, and the
split-index symplectic matrix `Matrix.J`. No real skew-orthogonal paired-basis
existence theorem was found. Its symplectic group is not an existence theorem
for an orthogonal change of basis. The source paragraph asserts the block form
and cites Takagi/Youla as alternatives; it prints no invariant-plane proof.

## Written foundation

`TNLean/Algebra/OrthogonalComplexStructure.lean` uses the existing
`LinearIsometry` type with the identity `J (J x) = -x`; it introduces no parallel
complex-structure or inner-product-space class. It proves skew-adjointness,
orthonormality of `x, -J x` for unit `x`, invariance of their span and its
orthogonal complement, and the square-minus-one identity on the restricted
isometry. The matrix action is the actual `Matrix.toEuclideanLin` action,
bundled through Mathlib's matrix/operator star algebra equivalence.

The order matters: `x, J x` gives the negative of the source's matrix `Y`;
`x, -J x` gives columns `J x = -(-J x)` and `J(-J x) = x`, hence
`Y = [[0,1],[-1,0]]`. The explicit index equivalence identifies the source's
paired form with **minus** Mathlib's split `Matrix.J`, then enumerates the pairs
on `Fin (2*m)`. No sign or split/interleaved identification is assumed.

## Paired basis and matrix assembly

`OrthogonalComplexStructureBasis.lean` now writes the dimension induction
constructing a complete orthonormal paired basis:
choose a unit vector, restrict to the invariant complement of its two-plane,
and combine the two-plane basis with the inductive complement basis. The
zero-dimensional case uses the empty orthonormal family. Spanning follows
from linear independence and the cardinality matching the finrank, using
Mathlib's existing basis constructor.

`OrthogonalSkewNormalForm.lean` reindexes that basis to `Fin (2*m)` and writes
`Matrix.exists_orthogonal_congruence_interleavedSkewForm`, with conclusion
`Oᵀ * Σ_m * O = A` and `O` real orthogonal. It uses Mathlib's change-of-basis
matrix identities. The only hypotheses are real orthogonality and skew
symmetry; no chosen pair decomposition is supplied by the caller.

`SkewUnitaryNormalForm.lean` combines this result with
`exists_skew_unitary_congruence` to write the direct complex Youla statement
`x = Uᵀ * Σ_m * U`. Its only hypotheses are skew symmetry and unitarity on
`Fin (2*m)`. The complex intermediate matrix's real-entry property supplies
an actual real matrix; real orthogonality and skew symmetry are transported
through the injective entrywise real-to-complex ring homomorphism. The final
unitary is the product of the complexified real orthogonal witness and the
existing symmetric unitary witness. No determinant assumption is introduced.

These are full source-level proof candidates for the missing matrix
normal-form obligation, not verification evidence. The separate full MPU
classification and its standard-form hypotheses are outside this slice.

## Verification boundary

The new source is written without local Lean builds or compilation at the
user's request. All new Blueprint ingredients and both normal-form nodes
remain `notready`; `corconj` is not promoted. The remaining acceptance work
is compilation, diagnostics repair, the package linters and declaration
checking before integration. No proof placeholders, axioms or persistent
Lean test fixtures are introduced.
