# A balanced interval tree with actual interleaved trims

`exists_physical_dg_interleaved_interval_tree` constructs one actual balanced
recursive tree from the original positive nearest-neighbour chain. The full
ground space G remains the global target. Each physical interval family and
the common reference are chosen before children, their merged dimension,
the retained sample dimension and Haar unitary. The nominal sample ceiling
is fixed by the chain and failure target (L+1)^(-2).

Every long parent uses the literal operation `sampledIntervalInterleavedTrim`:
select a successful Haar sample, then repeatedly apply the fixed family to
the CURRENT space and collectively trim that image. The actual selected
unitary is retained in a public equality for the actual recursive children.
The proof never identifies this operation with the earlier operator-word
image followed by only one final trim.

## Invariant and construction

A thin generic choice lemma, `exists_balanced_interval_tree_of_choices`,
constructs an operation from successful indexed parent candidates. It then
applies the existing `balancedIntervalSpace_invariant`. The physical
application uses actual Haar unitaries as the candidate indices, taking
one from the nonempty fixed-child event. It assumes no final viable spaces.

The invariant is the conjunction of 3/200-viability for the same G,
dimension at most M=D^6 s^3 and at most M recorded spanning vectors, each
with xi^2 times its internal-cut Schmidt rank at most M. Full leaves have
length at most 4ell; q^(4ell)<=D^6<=M and xi<=xiMax<=1 prove their bounds.
At every long parent the actual fixed-child event supplies the next actual
interleaved output. The invariant follows at EVERY valid interval, not only
at the full-chain root. Its ranks concern recorded vectors and retain the
whole-exterior reference rank Dref^2, not an unchanged bound on all vectors
of the span.

The source is ALVV, arXiv:1602.08828v2, Figure fig:merge-prime,
lines 1668–1670, and the induction in lines 1777–1817. The assignment and
integer-count corrections are documented in the existing approximation
parameter note. The proof retains block leaves, g=min(gamma,1), the fixed
nominal sampling scale and larger integer round count.

In particular ell=ceil C(v^6/g+sqrt(w)v^3/sqrt(g)), where
w=1+log r+2log(L+1). The honest SAME count D therefore depends on length
and ground dimension. It is not identified with the printed fixed-(q,g)
count profile. Quantitative simplification and efficient family comparisons
remain separate. No adaptive joint probability, energy-estimation invariant,
final spectral extraction or running time is asserted. The older common-root
refinement theorem concerns its own one-final-trim tree and is not silently
transferred to this different literal recursion.
