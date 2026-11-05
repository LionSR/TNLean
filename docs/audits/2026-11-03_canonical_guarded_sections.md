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

Default elaboration options were retained. The mathematical entry was rendered
and inspected. Ordinary combined compilation and compiled blueprint checking
remain integration checks. No shared source, artifact, cache, dependency pin,
or Mathlib source was changed or built.
