# PGVWC07 literal weighted-vector cancellation

Source: `Papers/quant-ph_0608197/MPSarchive.tex`, Theorem 4 at 742–762,
standing block assumptions at 1314–1330 and Theorem 11 (`2blocks.1`) at
1407–1422. Parent implementation: #10361. Tracking: #7684.

The word “different” has a material mathematical interpretation here.
Canonical data impose only individual block conditions. Theorem 3 gives
site-independent representations, Theorem 5 decomposes the period of one
block, and Theorem 6 describes its generic Schmidt spectrum. None imposes
pairwise gauge-phase separation. The canonical-construction proof stops
once each block has scalar fixed space; it does not merge equivalent blocks.

The actual example uses three bond-one tensors `(1,0)`, `(-1,0)`, `(0,1)`
with all weights one, common C1 length one and chain length thirteen. The
source bound is exactly `13 = 3 * (3 - 1) * (1 + 1) + 1`. The weighted
vectors are nonzero and pairwise unequal, but their sum is the normalized
all-one product vector. The actual one-site diagonal projection onto zero
annihilates that sum at every translated site. It fixes the all-zero
product vector at each translated site; positivity of the actual finite
sum therefore proves that the first block is not a ground vector.
No interaction identity, local equation, canonical data or kernel is supplied
as a hypothesis: they are constructed or derived in the production module.

This is a counterexample to the **literal weighted finite-vector reading**.
A projective meaning of “different states” excludes the opposite first two
components. The gap note records that distinction as a formulation-correction
candidate; it makes no claim about the authors' intended convention. No
counterexample to the separated-block theorem is asserted.

The final production theorem bundles the actual canonical data, common C1,
nonzero components, weighted-vector inequality, exact volume bound, normalized
sum, positive interaction, summed ground equation and failed first-block
equation. A full kernel-dimension theorem is unnecessary for the failure of
the first printed conclusion and is omitted.

Validation is source-only. No local Lean/Lake/build/elaboration/checkdecls
command ran. All new Blueprint links remain notready pending hosted acceptance.
