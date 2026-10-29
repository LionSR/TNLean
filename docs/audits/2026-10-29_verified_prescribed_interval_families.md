# Verified prescribed-interval families and logarithmic filters

The checked mathematical revision is TNLean
`c9516b84af92761e3863f632188b5655f43cd35f`, with QICLean
`92ceaab6274f9cb9bf226c20d144c4d0d83a5f83`. The results extend the
previously verified construction at `5cec1958d1`. All changes remain local.

## Sampling before the exact ground energy

For a known bracket [a,a+1], with 0 <= a <= n-1, the word length and sample
budget are chosen before every ground energy and normalized ground vector
in the bracket. The normalization cost is bounded by
n^2 exp(4(a+1) log(Q)/Delta). One actual unscaled sample supplies the norm
approximation, all letter counts, all spatial operator Schmidt ranks, and
cut factors chosen before every viable input family. Its relative projector
error is less than eta+1/Q; the resulting half-viable families have error
4(eta+1/Q), with the stated cardinality and bond bounds.

This does not select the bracket, prove a high success probability, or
establish an energy-independent running time. The published Methods allows
omission of the scalar normalization; the remaining choices and quantitative
scope are recorded in `lvv13_sampling_ground_energy.tex`.

## Logarithmic robustness and favorable scalar parameters

For the original positive-contraction nearest-neighbour chain, the physical
robustness and actual clipped-Hamiltonian filter now hold at
`t >= 1024+16 log(1/g)`. The required bound g <= 1 is derived from that
original unique-ground-state chain. It is not assumed for arbitrary
exteriors or degenerate spaces. The old polynomial-threshold statements
remain consequences with unchanged signatures.

A separate scalar theorem chooses a square degree and proves the strict
rank-contraction tradeoff, together with a logarithmic rank bound of order
(1+log q+log(1/g))^3/g. This is not yet a construction of the initial
product overlap or the moving-target iteration needed for the original
AKLV entropy theorem.

## Every prescribed interval

The ALVV improving family now exists on every prescribed interval of a
chain with L >= 2 and q >= 2. Inward cuts and actual clipped polynomials
handle long intervals, including endpoints. Configuration matrix units
handle short and empty intervals. The same family works before every
viable subspace, and is transported to the original spectral windows with
its explicit comparison loss.

With ell chosen from the capped width g=min(mu/(3 log L),1), the full count
uses D=(q ell^2)^(22 ell) and satisfies D^12 Delta < 10^(-5). The source-scale
count retains the positive part of the logarithm and the fixed density
bandwidth factor. The improving error and the original-window error remain
different quantities. In particular, comparison precision 1/200 already
contributes 1/100 to the latter error; a final original-window error of
1/100 is not claimed. Unequal nested-target sampling, the low-density
bootstrap and the binary tree remain open.

## Verification

The first combined revision, `222cb6583b`, passed a full 15,092-job build,
strict checks of 16 changed production files and five existing regressions,
and an imported foundation audit of 87 public declarations. Source and
compiled blueprint checks, added-prose checks and the forbidden-token check
also passed. Its new interval module took 53 seconds, exceeding the
unchanged 50-second compilation limit.

The regional construction lemma was then moved to its own module. Its
statement and proof were preserved exactly, apart from making the lemma
public; both interval-family headline statements and proofs were unchanged.
At the final mathematical revision, the full 15,093-job build, strict checks
of the three affected files and five existing regressions, an imported
audit of all three public declarations in the two construction modules,
and all documentation and timing checks passed. The two modules compiled
in 30 and 11 seconds. The former remains a 25-second warning, below the
50-second limit. Across the two audits, 88 distinct public declarations
use only `propext`, `Classical.choice` and `Quot.sound`.

The companion revision separately passed its full 10,348-job build, strict
checks, imported foundation audit and compiled blueprint checks. Neither
library rebuilt Mathlib from source. Existing caches and the repository
lock were used; no artifacts were copied from modified worktrees. No
permanent Lean test fixture was added.

The exact local records are `/tmp/tnlean-prescribed-intervals-gates.json`,
`/tmp/tnlean-regional-construction-split-gates.json`, and
`/tmp/qiclean-interval-and-spectrum-gates.json`. Completion marks added
after these checks affect documentation only; source synchronization and
compiled declaration checks are repeated for those marks.

The integration also adopts the upstream physical power-projector and
two-window polynomial rank results, and corrects the Hastings 2006 basis
status: estimates conditional on a supplied refinement do not construct
that refinement. These scoped results do not complete the three broader
area-law programmes.
