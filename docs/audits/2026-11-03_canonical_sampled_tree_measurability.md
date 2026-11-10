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
