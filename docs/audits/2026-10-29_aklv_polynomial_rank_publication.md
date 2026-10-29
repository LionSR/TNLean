# The AKLV polynomial Schmidt-rank estimate and physical filter

The formalization proves AKLV, arXiv:1301.1162v1, Section 4,
Lemma 4.2 (`l:agsp`), source `1dfrustrated34.tex`, lines 586–663,
and combines it with the Chebyshev filter of Lemma 4.1, lines 530–583.
For an L-site chain of local dimension q, write
G = H_L + sum_j H_j + H_R, where the s middle interactions have nearest-neighbor
support and the exterior operators have the corresponding left and right
supports. For s > 0, q > 0, and every polynomial P of degree at most ell,

`OSR(P(G)) ≤ (q * (ell + 1)) ^ (16 * (ell / s + sqrt(ell) + 1))`.

The divisions and square root in this exponent are natural-number operations.
For positive degree the source-base form is

`OSR(P(G)) ≤ (q * ell) ^ (96 * max (ell / s) (sqrt(ell)))`.

No positivity or spectral assumption is needed for the rank theorem. The proof
partitions actual ordered words by their frequencies, chooses a least frequent
middle interaction, transports the rank bound to the original central cut, and
shortens the interaction window without changing the Hamiltonian or that cut.
It includes degree zero, odd window lengths, and local dimension one.

For Hermitian G with a unit ground vector, positive projector gap, and spectral
upper bound, the constructed degree-ell real Chebyshev polynomial fixes the
ground vector. Its evaluation at G has the preceding rank bound and norm error
at most `2 * exp (-2 * ell * sqrt (gap / (upper - E0)))` from the ground projection.
The squared suppression estimate applies to every orthogonal unit vector.

The commuting-gap coefficient retains the corrected binomial count documented
in https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
Its matrix, counting, and Chebyshev results are supplied by QICLean PR #1005,
pinned at `ae966f98ecaa3b9b959bed1a4afa6361d6d993ef`.

This submission contains the polynomial and spectral-filter estimates.
Hard-truncation robustness, optimized entropy bounds, and final MPS
approximation are separate mathematical developments.

## Verification

The isolated target build completed successfully (3,442 jobs), using the
canonical locked build command and prebuilt Mathlib cache. All nine extracted
modules compiled against the published QICLean revision. Blueprint/source
synchronization, active mathematical references, generated imports, file-length
checks, and root/docbuild manifest agreement pass. Source checks find no proof
placeholders or added axioms.

The full-library build and final strict/declaration checks are recorded in the
pull request when complete. Four existing blueprint-role mismatches in
`ch35_aklv_energy_truncation.tex` also occur at the base revision; the new chapter
has two headline theorems and uses lemmas for its supporting results.

The extraction preserves current-main definitions and does not copy build
artifacts from the integration checkout.

## Compatibility with the current QICLean library

The pinned revision already provides
`Kraus.isNBlkInjective_of_isNBlkInjective_conjTranspose` in
`QICLean/Kraus/Injectivity.lean`. Its identical local declaration in
`TNLean/MPS/Core/Blocking.lean` is removed to avoid declaring the name twice.
Existing callers and the blueprint retain the same theorem name and statement.
