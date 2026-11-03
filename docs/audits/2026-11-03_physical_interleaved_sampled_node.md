# A fixed-child sampled node with interleaved collective trims

The actual operation `sampledIntervalInterleavedTrim` takes the Haar sample
of the adjacent-coordinate tensor merge, then applies the fixed physical
family to the current space and collectively trims at every round. It is
not an operator-word image with only one final trim.

The physical theorem constructs its actual clipped target, family and common
reference before every pair of children, merged dimension, retained sample
dimension and Haar unitary. The nominal ceiling s is fixed by the original
chain and failure target (L+1)^(-2), before choosing the family. There is no
uniformity over arbitrary smaller failure targets or all nominal sample
sizes. It retains the independent truncation/polynomial scales, count D,
overlap a and tiny original/clipped/reference accuracy of the calibrated
family theorem.

For two children viable 3/200 for the same full original ground space and of
dimension at most M=D^6 s^3, the actual merge has dimension Q<=D^12 s^6 and
is 1/4-viable for the clipped target. The corrected complex-sphere event gives
success at least 3 min(s,Q)/(32Q)>=a, with failure at most (L+1)^(-2).
It is a measurable event for each FIXED child pair. Every successful unitary
produces the literal interleaved output, which has dimension at most M,
at most M actual recorded generators with weighted internal-cut rank at most
M, and error at most 1/200 for the clipped target and 3/200 for original G.
The long parent ensures L>0, so the success event is explicitly nonempty.

The corrected sampling scale and exponent are cited in the source. The
reference retains the whole exterior and its squared bond rank. The initial
sampling, clipping comparison, physical filter, reference and stopping
conditions are all derived from the physical hypotheses; no separate
sampling or trimming conclusion is assumed. The genuine input assumptions
are the viability and dimension bounds on the two children.

This supports ALVV, arXiv:1602.08828v2, Lemma l:rs, lines 530–558,
Figure fig:merge-prime, lines 1668–1670, and lines 1797–1805. Long intervals,
capped-gap estimates and the larger integer count remain explicit. This is
one fixed-child node theorem, not an adaptive measurable tree law or a
running-time claim.

## Verification

The immutable provider was TNLean 478e8a08f8d97cec4064070a29170a0953362d3e
with its own QICLean 9578336a5123a76001a1218e271132091c828de2. Private overrides
were exactly frozen QICLean 731e9c2ffec00be39fef8fe6d68072ea7ccbba72 and TNLean
9d124cba60d3be846d042883de9af8e7d4c4af8c. The source worktree contains no .lake.
Selected source/object pairs, root inputs, Mathlib artifact and changed
importer provenance were guarded. No provider or cache artifacts were
modified or copied.

The final strict check passed in 15.343 seconds with 747 protected pairs.
An imported inspection of the definition and theorem passed in 9.409 seconds
with 748 pairs, depending only on propext, Classical.choice and Quot.sound.
The temporary source was deleted. Blueprint/source coverage with the
read-only pinned dependencies, roles, reader-facing prose, generated imports,
forbidden proof tokens and whitespace were checked. Ordinary combined builds
and compiled blueprint validation remain integration gates.
