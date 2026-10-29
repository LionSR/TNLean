# Verified physical detectability and periodic interaction families

The checked mathematical revision is TNLean
`e46d137d7784b6b4abf6155f68d1cb8e6dbc2cd1`, with QICLean pinned to
`afcf986970504f1d370e475f0617256ca83b160d`. The companion mathematical
source was checked at `1aa1011b4f5518d59de4ef462b71d84ad4ec33ea`;
the pinned successor records completion in documentation only. The later
QICLean revision `df17465b` changes only a paper-gap note's page margins.
All work remains local.

## Physical projection chains

The actual even/odd product is constructed from supported nearest-neighbour
orthogonal projections. The count of noncommuting neighbours is derived
from the bonds, including endpoints and padded zero terms. Each parity
product is an orthogonal projection. The actual product fixes the full
ground kernel and preserves its orthogonal complement, without assuming
that the kernel has dimension one.

The energy estimate holds homogeneously for every vector. The converse
holds for every unit vector with constant three. Above a unique
frustration-free ground state with positive gap gamma, the squared
contraction is at most 4/(4+gamma); no upper bound on gamma is used.
Reduction from positive contractions to range projections, and the
regional truncated Hamiltonian with its spectral and rank estimates,
remain separate constructions.

## Physical periodic interaction families

On a ring of 2N ell sites, the truncated Gaussian filters and neighbouring
coarse pairs are constructed from the original local interactions. The
construction includes the closing pair. It derives supports, Hermiticity,
norm bounds, local residuals and total approximation error at most
2N ell epsilon_local. The error retains the actual omitted-shell count.
The lower operator comparison uses the same original ground projector.

The statement treats a unique ground vector and regular nonempty periodic
blocks. It does not construct the general hierarchy, degenerate-basis
refinement, final tensor bond bounds or the local thermal index estimate.
The two geometric modules preserve their existing primary-worktree
mathematical declarations and proofs; only the imports were adapted to
the checked construction.

## Normalization and scalar soft truncation

The companion results construct the actual phase-aligned normalized
filtered image, with its residual-to-overlap error and actual Schmidt-rank
growth. They do not assume a normalized input. Physical product-overlap
initialization and the subsequent moving-target sequence remain open.

The scalar soft truncation is recovered from draft 981 with its strict
proof correction and corrected cap t(1+log m). In addition to the
polynomial remainder, the geometric remainder and exponential-weight
estimate are proved. For m>=1, x>=0 and 0<theta<=1/2,

    x-h_(m,m)(x) <= (2/theta) exp(theta*x-theta*m/2).

Application to a physical regional operator requires a separately derived
exponential moment. The source's first uniform energy estimate is false
on a nondegenerate three-qubit family with fixed spectral gap 1/2.
The exact, independently reviewed calculation is recorded in
`docs/paper-gaps/alvv16_soft_truncation_energy_estimate.tex`. It is not a
Lean counterexample theorem and does not refute all later spectral or
approximation conclusions. A corrected physical spectral comparison and
a sufficient cluster/MPO estimate remain open.

## Verification

The exact TNLean mathematical revision passed:

- The full 15,099-job library build.
- Strict checks of six changed production files and five existing regressions.
- An imported foundation audit of all 42 public declarations in the four new
  mathematical modules, using only propext, Classical.choice and Quot.sound.
- Source synchronization, compiled blueprint declaration checks, added-prose,
  forbidden-token and compilation-time checks.

No job in this full build reached the 25-second warning threshold. The
companion revision separately passed a full 10,350-job build, strict checks
of four changed files, and an imported audit of all six public declarations
in the two new modules, with the same standard three axioms. Its source
and compiled blueprint checks, prose and timing checks also passed.
Neither library compiled Mathlib from source. Existing prebuilt artifacts
and the repository lock were used; no cache artifacts were copied from a
modified worktree. No permanent Lean test fixture was added.

Both paper-gap notes were rendered and visually inspected. The new energy
counterexample occupies three pages. The recovered scalar-cap note fits
one page after a margins-only correction, with all mathematics unchanged.
There were no unresolved citations, missing glyphs or layout overlaps.

The local complete records are `/tmp/tnlean-detectability-periodic-gates.json`
and `/tmp/qiclean-filter-normalization-soft-gates.json`. Subsequent completion
records change documentation only. The three broader area-law programmes
remain active; these bounded constructions are not their completion.
