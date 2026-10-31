# Actual W-vector blocking and prime-divisor bounds

Source context: `Papers/quant-ph_0608197/MPSarchive.tex:2090–2097`, the blocking
device, and `Papers/2011.12127/TN-Review-main.tex:2348–2362`, the actual W vector.
These are elementary derived identities, not additional claims attributed verbatim
to those sources. Tracking issue: #2947. Base: main `c7d2992c8`.

The production module reuses `wIndicator`, `pvbsVacuum`, the PVBS recurrence at
parameter one and the existing blocked physical alphabet/flattening equivalence.
There is no parallel W-state family or geometry framework. The squared norm of
W is derived by splitting the first qubit, and the two actual columns of the
local encoding are proved orthonormal. Existing rectangular Kronecker algebra
then supplies the Gram identity of every tensor power.

The global encoding identity is derived from the actual excitation counts of
concatenated block words. It states `(tensor U_k) W_m = W_(m*k)/sqrt(k)`; after
normalization it maps the actual unit W vector to the actual unit W vector on
all `m*k` physical sites. No coefficient or blocked-state equation is supplied
as a premise.

An actual periodic tensor representing `c W_(m*k)` compresses by the adjoint
physical map of its blocked tensor to `c sqrt(k) W_m`, with the original bond
dimension. The existing arbitrary-tensor prime-length theorem applies to this
compressed tensor. Therefore every prime divisor of a represented positive
length obeys the previous explicit fifth-degree bound. This gives new information
at lengths such as twice a large prime, beyond the old no-small-divisor regime.

The result does not show that compression preserves C1 or primitive blocks,
does not control a least common multiple of surviving periods, and does not
bound the original length when all its prime factors are small. The general
single-length `D^3 log D` theorem and the generic logarithmic Wielandt estimate
remain open. The fixed-interaction model #10420 and literal weighted-vector
counterexample #10426 are separate results.

Validation is source-only. No local Lean/Lake/build/elaboration/checkdecls command
ran. New Blueprint statements and proofs remain notready pending exact-head
hosted acceptance. Two independent mathematical and pinned-API reviews passed.
One review found a reversed matrix-action reassociation in the compression proof;
it now uses the pinned forward `Matrix.mulVec_mulVec` orientation. Unnecessary
positive-length hypotheses were removed from the rescaled identity, which also
holds algebraically at zero; positivity is retained where it supplies an actual
unit vector or isometry. Native imports, full Blueprint synchronization and
reverse public-declaration coverage, duplicate tags, roles, configured ChkTeX,
prose, source integrity, module size, 100-column width and whitespace checks pass.
