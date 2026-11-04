# Actual local projectors and varying-bond OBC sections

Source: PGVWC07, `Papers/quant-ph_0608197/MPSarchive.tex`, Theorem 9 statement
and proof, lines 1195–1222. The local range is the trace range of the actual
rectangular product at two adjacent sites. The proof's first step passes from
the kernel of the positive local Hamiltonian to fixed-outside pair sections.

`VaryingOBCProjectorKernel.lean` supplies precisely that step on the same raw
varying bond sequence and rectangular families as the preceding reconstruction.
It introduces no chain record or second canonical predicate. The pair boundary
map uses Mathlib's rectangular multiplication linear map and trace functional;
its range is projected onto its orthogonal complement with Mathlib's standard
orthogonal projection.

For an ordered prefix and suffix, the coordinate restriction fixes each outside
letter and retains only the two adjacent physical coordinates. The Hamiltonian
is the sum of the adjoint compressions R† P R. Every outside configuration is
counted once. This is the identity extension of each pair projector, without
periodic wrapping and without the averaging factor required by restrictions
which redundantly index the active letters too. The finite indexing subtype
lists exactly the nonnegative prefix/suffix lengths with p+2+q=N.

QICLean's existing positive-sum kernel theorem is applied to these actual
compressions. Its conclusion and the positive quadratic-zero theorem give the
pair-projector kernel condition. The orthogonal projection kernel then produces
actual rectangular boundary matrices. The reverse implication is also proved.
The public list-coordinate equivalence matches the hpair condition of
`obc_trace_reconstruction_of_adjacent_pair_sections` exactly. Its coefficient
identification is only equality between the list and Fin descriptions of the
same state, not an additional physical assumption.

Neither C1 nor canonical row normalization is needed for this local kernel
identification. Those assumptions remain explicit in the preceding full-chain
reconstruction. The final N≥2 scalar-endpoint Hamiltonian kernel equality still
requires their assembly and identification of the represented state; this
module does not claim it separately or assert literal equality of normalized
vectors of different phases. The unrestricted source statement is not promoted.

No Lean, Lake, elaboration or build was run. All new Blueprint nodes and proofs
remain notready. Native checks cover generated imports, declaration ownership,
mathematical roles, reader-facing prose, proof integrity, whitespace and width.
This branch includes the unchanged AKLV role-only baseline from draft #10359;
no AKLV mathematics is changed.

## Actual boundary states and the reverse inclusion

`VaryingOBCBoundaryStates.lean` supplies the other inclusion needed by the final
assembly. It proves concatenation for actual rectangular products by induction
on the suffix length, reusing the existing last-letter product identity. For an
arbitrary endpoint boundary Z, the actual trace vector has pair boundary
X=P_suffix Z P_prefix. Rectangular trace cyclicity gives the coefficients, and
the actual projector-kernel characterization proves H applied to this trace
vector is zero. No injectivity, canonical normalization, or supplied local
annihilation condition occurs in this direction.

The relevant Mathlib source files were independently byte-compared against
objects at manifest revision c55e6e786f49471c72fbddbec5415808896aec1e, including
the finite tuples, list words, rectangular trace, projections, positivity and
adjoint APIs. The shared source snapshot agrees with those objects. This is
source provenance and API review, not compilation evidence.
