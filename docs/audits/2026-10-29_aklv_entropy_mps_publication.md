# Entropy and matrix product approximation from AKLV filters

This development proves two consequences of the physical AKLV construction
for a finite nearest-neighbour chain with positive-contraction interactions,
a unique unit ground vector, and actual first excitation gap `g > 0`.
The universal constants are chosen before the chain, its local dimension,
the Hamiltonian, and the requested approximation accuracy.

Writing `u = 1 + log q + log (1/g)`, the entropy at every cut is at most
`C u³/g`. For `0 < epsilon ≤ 1`, put
`z = log (2048 (L+1)/epsilon²)`. There is a normalized open-boundary matrix
product approximation at distance at most `epsilon`, with bond dimension
satisfying

`log D ≤ C (u³/g + (z³/g)^(1/4) (u + log(z+1)))`.

The approximation is the normalized ordered product of the leading regional
spectral projections applied to the ground vector. The proof establishes
that this product is nonzero and bounds its Schmidt ranks. It does not
assert an algorithmic running time.

## Mathematical construction and source scope

The source is AKLV, arXiv:1301.1162v1, `1dfrustrated34.tex`: the physical
normalization and truncation theorem at lines 879–963, the changing-target
sequence and entropy summation at lines 1003–1075, and the accuracy-dependent
window argument at lines 1503–1517. The rank estimates are those submitted
separately in TNLean PR #10390.

Disjoint regional ground energies determine the scalar shifts. Two exterior
spectral clippings preserve a gap of at least `9g/10` above the logarithmic
threshold `1024 + 16 log(1/g)`. Actual Chebyshev filters produce a normalized
initial vector and successive normalized images with dyadic errors.
Their multiplicative Schmidt-rank bounds give the marginal tails used in
the finite entropy sum. Enlarging the central window according to the
requested accuracy yields the fourth-root term in the approximation bound.
When a centered window does not fit, the smaller-side dimension gives the
required exact rank estimate. Thus neither final theorem assumes that a
window fits, supplies a filter or rank schedule as a hypothesis, or invokes
an independent area-law theorem.

The signatures require that `mu + g` belongs to the spectrum, in addition
to the projector lower bound. They retain logarithms of the inverse gap.
These qualifications are explicit in the blueprint statements and module
documentation. The corrections to exterior support, the inclusive bulk
normalization, and the printed rank summary are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`. The submission does not
claim the entropy estimate without the displayed inverse-gap logarithms.

The logarithmic cutoff and coherent sequence distinguish this result from
the inverse-gap cutoff developments in PRs #10331 and #10371.

## Provenance and dependencies

The 33 affected mathematical modules were extracted from TNLean revision
`9ad6cdd3c23da0ce9b5e6cc36edfec99f0211ff7`. The extraction excludes the
unrelated additions to `PolynomialFilterParameters.lean`. It copies source
files, not compiled artifacts, and preserves the current public definitions.

Root and documentation manifests both pin QICLean revision
`716753c025d95fe36e3dc8f421571c81754adaaf`. This revision combines the
necessary files from public PRs #978, #979, #1005, #1006, #1007, and #1008.
Its audit `docs/audits/2026-10-29_aklv_published_prerequisites.md` identifies
the exact source revision of each added file. Those PRs remain the units
of review; this combined revision introduces no further mathematical proof.

The existing `Entropy.localLift_sub` declaration is supplied by
`QICLean.Representation.RelativePin`. Its duplicate local definition is
removed from `SequentialTruncation.lean`, preserving the theorem name and
statement. The monotonicity of the allowed open-MPS bond dimension is also
included; the same elementary result occurs in the separate LVV submission.

Likewise, `WordMultiplicity.wordCoefficient` is now supplied by
`QICLean.Algebra.WordCoefficient`. The identical definition is removed from
`TNLean/Algebra/TwoMarkerScalarRecovery.lean`, which imports the companion
module. The ordered-word sum, public name, and existing consumers are unchanged.

## Verification

The two final target modules compiled successfully with the locked Lake
command and the prebuilt Mathlib cache (4,268 jobs). All 33 affected
mathematical modules passed a separate elaboration with strict implicit
arguments, the Mathlib standard linter set, and warnings treated as errors.
The slowest such check took 19.14 seconds.

All 94 new declarations cited by the AKLV and regional blueprint sections
were checked against the compiled imports. Their axiom sets contain only
`propext`, `Classical.choice`, and `Quot.sound`. Generated imports, module
lengths, root/documentation manifest agreement, blueprint/source
synchronization, and active mathematical references pass. The scoped
tactic-pattern scan reports no repeated patterns. Full-library and rendered
documentation results are recorded in the pull request when complete.

The four pre-existing blueprint-role discrepancies in
`ch35_aklv_energy_truncation.tex` are outside this change. The new chapter
designates exactly two main theorems.
