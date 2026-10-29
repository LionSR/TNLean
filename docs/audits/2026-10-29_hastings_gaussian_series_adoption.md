# Adoption of the Gaussian commutator expansion

Issue: #10397, under #9828. Source: Hastings,
`References/cond-mat_0508554/proj3new.tex:1005–1009`.

The existing Gaussian variational lower bound already uses the actual
Gaussian integral and is proved on the previous QICLean pin. This change
adds the missing public identification of that exact filtered operator
with the exponential and the norm-convergent even-commutator series. It
reuses the existing filter and `GaussianFilter.commutatorCLM`.

The coefficient at commutator order 2r is
`(-q/(2 ΔE²))^r/r!`. The printed variance power is corrected by the
QICLean-owned note at
https://sirui-lu.com/QICLean/paper-gaps/hastings05_gaussian_series_coefficients.pdf.
No local copy of that note is introduced.

## Dependency and publication status

The candidate pin is exact QICLean revision
`8774105cf88a452a92e3c03de664733e7a15caca`, supplied by
https://github.com/LionSR/QICLean/pull/985. That PR remains open, so this
adoption stays a draft pending review/integration of the dependency and
publication of its note. It must not be merged automatically. The Lean
source, dependency manifest and toolchain of the QICLean change were
compared against the previous pin; the QICLean manifest and toolchain are
unchanged. Both TNLean pin fields and the declared Lake requirement use
the same exact revision.

The new Blueprint lemma and proof remain `notready`. Native declaration
synchronization can inspect the exact QICLean source revision without
mutating any warmed build cache. No local Lean, Lake, build or checkdecls
command was run, as requested. The hosted success of the dependency does
not validate the two new TNLean specializations; their own hosted
acceptance remains pending.

Independent bounded source/API review checked both specializations against
the exact candidate QICLean source, including the NNReal-to-complex coercion,
operator-norm instance and coefficient orientation, and found no concrete
mismatch. All native import, role, duplicate-tag/declaration synchronization,
prose, TeX, source-integrity, file-size and whitespace checks pass. The
pre-existing role repair #10359 is included as a separate baseline commit.
