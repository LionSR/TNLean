# True guarded sections of the sampled interval recursion

At a fixed valid long parent and a fixed whole seed, the baseline children
are the actual midpoint children of the existing balanced recursion. Changing
the parent's strictly longer interval coordinate preserves both children.
The updated parent is exactly the existing canonical sampled interleaved
operation applied to that same adjacent child pair and the new seed.

The new theorem assumes a fixed-child true-failure bound only when both
baseline children are viable for the same original global target. If either
child is not viable, the true guarded section is empty. Otherwise it is
contained in the actual fixed-child parent failure event. This proves the
requested section bound by measure monotonicity. No measurability premise,
chosen hull, independence assertion, or comparison of orthonormal sampling
bases is used. All regional targets retain the entire original exterior.
The supplied families and parameters precede the whole seed.

This is a conditional auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1` and lines 1777–1817. The fixed-child bound is an explicit
analytic premise and is not asserted here for an arbitrary family.

The actual-name strict check passed in 6.010 seconds against immutable
TNLean `435cbe7fe53e5d3a04c1b8eb2382753749f21a64` and its own QICLean
`b2ea12a0139820758e161514968ed9ead661c5a7` package, with the frozen actual
sampled-tree and parent-section results as explicit source/object overrides.
All 180 selected dependency pairs and the build inputs were guarded.
An imported one-name foundation audit passed in 6.800 seconds using only
`propext`, `Classical.choice`, and `Quot.sound`; its temporary source was
deleted. Default elaboration options were retained. Source/blueprint
synchronization, reader prose, generated imports, proof integrity,
whitespace and pattern checks passed. The mathematical entry was rendered
and inspected. Ordinary combined compilation and compiled blueprint
checking remain integration checks. No shared source, artifact, cache,
dependency pin, or Mathlib source was changed or built.
