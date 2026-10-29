# The actual regional frustration-free truncation

For a finite nearest-neighbour chain of orthogonal projections, the actual
regional construction retains each outside bond and replaces the two
internal parity layers by the complements of their existing physical
projection products. The resulting Hamiltonian is positive, has exactly
the full kernel of the original Hamiltonian, and has internal replacement
norm at most two. Empty intervals, endpoint intervals, zero vectors and
all finite local dimensions are included. Neither a distinguished ground
vector, uniqueness nor a spectral gap is assumed.

The source is ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`,
lines 1467–1487 and 1543–1550. These results concern the actual operator,
rather than a family satisfying supplied positivity or kernel conditions.
The source theorem's gap and rank conclusions are separate remaining
results. In particular, the printed universal rank bound is false; the
corrected bound is d²+3, as documented in
`docs/paper-gaps/alvv16_frustration_free_truncation_rank.tex`.
No rank theorem is asserted here.

The kernel argument uses the existing QICLean theorem on kernels of finite
sums of symmetric projections and the checked fixed-space characterization
of physical parity products. The outside bond terms and the two regional
complements form a single finite family of actual projections. Vanishing
of their sum forces every term to vanish; the two parity conditions
recover every internal bond. Conversely, the original common kernel is
fixed by both internal parity products. Mathlib's existing finite-sum
positivity and projection norm estimates give the other conclusions.

The private strict check passed in 5.556 seconds against TNLean
`bc299f74db315cdb8a077e0b678c0eba1f7e0028` and QICLean
`34cb0c3a24a9cfb8073e1fe7bb1087bc409fb951`. A separate import of the actual
compiled module audited all five public declarations in 4.298 seconds;
only `propext`, `Classical.choice` and `Quot.sound` occur. The 52 selected
imported TNLean/QICLean source/object pairs, build inputs, and Mathlib
sentinel remained byte-identical. The records and private objects are
under `/tmp/tnlean-frustration-free-regional-20261029`.

The source-only worktree has no Lake cache. No provider, package checkout,
pin or ordinary build artifact was changed, and Mathlib was not rebuilt.
Ordinary combined verification and the compiled blueprint declaration
check remain for coordinated integration. The spectral gap, same-parity
regrouping, and corrected tensor-rank bound remain subsequent work.

## Completed combined verification

TNLean `da3ab8dcc9` and QICLean `4276de2e` passed full builds, strict
checks, imported foundation audits and compiled blueprint checks. The
complete phase records, timing qualifications and remaining scope are
recorded in [the integration audit](2026-10-29_verified_soft_residual_refinement_range.md).
