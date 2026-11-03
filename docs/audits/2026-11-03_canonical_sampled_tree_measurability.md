# Joint measurability and coordinate dependence of the actual sampled tree

The new theorem concerns exactly balancedIntervalSpace applied to the frozen
canonicalIntervalSamplingOperation. It does not define a second recursive
model. Families, sample count, trimming threshold and round parameters are
fixed before the interval choices.

For every valid interval, its actual ambient orthogonal projection is
jointly Borel in the entire finite product of interval sampling coordinates.
The actual retained subspace depends only on coordinates whose interval
lengths are at most its own. Dependence is expressed with Mathlib's DependsOn
predicate. Replacing any strictly longer coordinate leaves that same
subspace unchanged. In particular, either strictly shorter child is
unchanged when its parent's fresh coordinate is replaced.

The true viability event is also Borel for any fixed full-chain target and
real error parameter, in the original regional tensor coordinates with the
whole interval exterior retained. No measurable comparison space or separate
probability event is substituted.

## Proof

A single private strong induction on interval length proves joint projection
measurability and coordinate dependence simultaneously. At a short interval,
the actual balanced space is the full local space and hence constant. At a
long interval, both midpoint children are valid and strictly shorter.
Their actual projections are Borel by induction. The existing adjacent
merge theorem gives a Borel candidate projection, and the already-proved
canonical sampled-parent theorem is jointly Borel in that actual candidate
and its unitary-product coordinate. Composition with the appropriate product
coordinate evaluation gives the actual parent projection.

If two choice families agree at all lengths at most the parent length,
the induction identifies their actual two children. Their parent coordinate
also agrees, so the literal canonical parent spaces agree. Mathlib's
dependent-function update identity then gives invariance under changing
any strictly longer coordinate. The generic tensor-projection test turns
the proved ambient projection measurability into the stated true viability
event for the same fixed target.

The theorem has no positive-dimension, nonzero-rank, spectral-gap, input
viability, local-success or probability-bound hypothesis. Endpoint cuts,
short roots, intervals of length zero and zero-dimensional spaces are
included. The positive leaf width is used only for strict descent of the
two children at a long root. Coordinate lengths are natural differences;
including unused coordinates in the dependence set causes no restriction
on the sampling law.

The source context is ALVV, arXiv:1602.08828v2, Figure fig:algo1 at
lines 1777–1817 and Figure fig:merge-prime at lines 1668–1670. This is a
measurability and dependence auxiliary. Conditional failure estimates,
their summation, literal soft Generate and a running-time theorem are
separate obligations.

## Provenance and verification

The proper source-only TN worktree starts from the checked TN
435cbe7fe53e5d3a04c1b8eb2382753749f21a64. Its dependency commits are the
frozen interval law fb1e4ac27e, canonical operation c6a3e88eb9, and literal
parent Borel theorem 222d3719df, cherry-picked without build artifacts.
Those dependency sources are unchanged. The worktree has no .lake directory.
Only the new tree module and its documentation form this contribution.

The private checker reads the immutable warmed provider at the same TN
commit with its own QIC b2ea12a0139820758e161514968ed9ead661c5a7. Explicit
checked source/object overrides supply the frozen root law, canonical
operation, actual family-image projection and two literal-parent leaves.
Every changed selected importer is re-elaborated; none is silently reused
with a changed dependency. Exact provider heads, clean state, build inputs,
selected source/object hashes and the prebuilt Mathlib artifact hash are
verified before and after checking. Provider sources, HEAD and build
artifacts are unchanged; no Mathlib source is compiled.

The actual-name strict check passes in 5.929 seconds with 176 guarded
source/object pairs. The imported audit of all four public declarations
passes in 5.294 seconds with 177 pairs. All depend only on propext,
Classical.choice and Quot.sound. The temporary audit commands are deleted.
All outputs and detailed guards are confined to
/tmp/tnlean-sampled-tree-borel-20261103. No production fixture or diagnostic
command is added.

The external manifest records source hashes and the source-only blueprint,
import, role, prose, forbidden-token, whitespace and dependency-label checks.
The ordinary locked build and compiled blueprint checks remain for
coordinated integration with the already-frozen dependencies.
