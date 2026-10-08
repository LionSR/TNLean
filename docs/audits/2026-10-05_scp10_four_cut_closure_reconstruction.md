# Actual four-cut closure equality with independent matching bond representations

The later [dimension-independent theorem](2026-10-05_scp10_full_four_cut_closure.md)
removes the common-alphabet restriction recorded by this intermediate audit.

Source: SCP10, arXiv:1001.3807, Theorem 5.5,
`Papers/1001.3807/paper_v3.tex`, lines 1421–1513.

## Proved statement

`fourTorusCutSpace_eq_matchedCommutingClosureSpan` identifies the intersection
of the four actual cut-map ranges with the span of actual commuting native
closure vectors. It applies to independent physical tensors at all four
sites and independently chosen matching semi-regular representations on all
eight oriented bonds of the native two-by-two torus.

The hypotheses are:

- a finite group;
- one finite virtual coordinate alphabet `V` and one finite physical alphabet;
- algebraic semi-regularity on each of the eight actual bond representations;
- G-injectivity of each physical tensor for the four-leg action made from its
  actual incident bond representations, with heads incoming and tails dualized.

Unitarity, G-isometry, homogeneous tensors, uniform bond representations,
parent-kernel classification, and a supplied closure-spanning equality are
not required. Unitarity from the source is therefore harmlessly stronger than
the algebraic assumptions here.

The conclusion concerns the real four-block edge cuts. There is no use of the
simple graph of the two-by-two torus, which would collapse parallel bonds.
Every cut domain permits one arbitrary joint tensor on its eight endpoint
indices. The initial regression includes an explicit correlated tensor that
cannot be written as a product of independent bond matrices.

## Proof dependencies and noncircular route

1. `TorusCutBoundaryBasis`: every fixed-boundary basis tensor is exactly a
   product of matrix units on the cut bonds. Arbitrary boundaries are their
   linear span; no factorization of an arbitrary boundary is assumed.
2. `TorusMatchedProjectorExpansion`: expanding the actual canonical contraction
   gives one group label per site. Each uncut physical bond is a relative
   representation matrix for that bond's independently assigned representation.
3. `TorusCutBondSupport` and `PhysicalProductFamilyRangeSupport`: fixing all
   other physical bond coordinates leaves a slice in that representation's
   matrix span. The four cuts cover every physical bond with an uncut bond.
   The slice criterion therefore derives full product support.
4. `TorusCutCanonicalBondSpan`: every actual canonical four-cut vector has a
   coherent expansion in products of the eight representation matrices.
   This is an output of the preceding support argument, not a premise.
5. `TorusCutFlatCoefficients`: source trace-dual extraction computes each
   coherent coefficient. If a plaquette equation fails, every vertex-label
   summand in the corresponding cut contraction contains a vanishing bond
   pairing. Thus the coefficient vanishes for every nonflat label assignment.
6. `TorusBondFlatConnection`: flat assignments on the actual labelled torus
   are vertex-gauge equivalent to two commuting seams. The general group-valued
   rooted-tree proof applies at period two and preserves all eight bonds.
7. `TorusCutAverageProjection`: the product of local invariant projectors
   fixes each canonical cut vector. It maps each bare bond product to the
   actual canonical network with those bond matrices.
8. `TorusCutClosureReconstruction`: project the derived flat expansion.
   Vertex-gauge invariance sends each surviving summand to an actual commuting
   closure. This proves the reverse inclusion. The existing explicit boundary
   witnesses prove the forward inclusion.
9. `TorusCutLocalInverse`: a common product of genuine local G-injective
   inverses identifies the four-cut intersection with the image of its
   canonical counterpart. The original site maps also recover the exact
   commuting closure span, proving the final theorem for independent tensors.

The proof uses coefficient extraction before making label-support claims, so
it remains valid for arbitrary coherent sums and cancellations.

## Remaining source-generalization boundary

The virtual coordinate type is currently the same at every bond, and the
physical coordinate type is the same at every site. The values of the bond
representations and the four site tensors may all differ. Equal alphabets are
an explicit dimensional restriction; the full source theorem with arbitrary
bond dimensions should not yet be marked formalized solely from this theorem.

The remaining extension is to dependent bond alphabets and physical alphabets.
It needs an edge-labelled dependent contraction model retaining the parallel
bonds, not a substitution by a simple-graph regional map. The mathematical
support, extraction, flatness, and averaging argument already permits distinct
bond representations; their coordinate types must next be made dependent.

This result supersedes the reverse-inclusion gap recorded at the earlier
foundation commit in `2026-10-05_scp10_four_cut_boundary_progress.md`, within
the explicit common-alphabet scope above.

## Validation

The source packet is checked with the pinned Lean toolchain, strict implicit
arguments, Mathlib standard linters, and warnings as errors. The new
`TNLeanTest/PEPS/FourTorusCutClosure.lean` checks:

- the full capstone with independent tensors and bond representations;
- a genuinely nonregular representation (trivial multiplicity two);
- exclusion of a nonflat bare bond product from the four-cut intersection;
- a concrete noncommuting S3 seam obstruction;
- guarded axiom reports for the capstone, derived bond expansion, and nonflat
  coefficient elimination, each containing only `propext`, `Classical.choice`,
  and `Quot.sound`.

The earlier correlated-boundary, matching-bond, native two-torus gauge, and
heterogeneous-product support regressions remain part of the validation set.
No shared import routers, source-labelled blueprint assertions, or external
branches are changed by this packet.
