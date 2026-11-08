# Quadratic solution over the prescribed OBC window

Source: PGVWC07, arXiv:quant-ph/0608197, MPSarchive.tex lines 1139–1169.
This child stacks the actual OBC prefix-factor source from draft #10370 and
the physical cut-window construction from draft #10381. The unpublished
dependencies are actual Git ancestry, not imports presented as main APIs.

The supplied tensor B is an actual OBC representation of the prescribed
length-N vector of a C1 TI tensor A. Its common bond bound is D²,
as in the source's bounded OBC window. C1 proves physical window rank D²;
the universal rank lower bound and B's type bound force every endpoint and
internal window bond to be exactly D². No bond equality is assumed.

OBCMinimalPrefixBasis proves that the original physical prefix columns at
any minimal bond are independent and span the actual cut column space.
Its slicing matrix between two minimal bonds equals the original supplied
site matrix, by the original adjacent-prefix recursion. Thus the bases
and the local identity are derived from the actual representation.

QuadraticPrescribedOBCWindow proves the supplied original window equals
the physical slicing window in these derived bases. Applying the existing
basis-independent construction gives an actual quadratic solution for this
very window. No alternate OBC tensor, uniqueness argument, comparison
gauge, quadratic solution or endpoint identity is substituted as a premise.
Canonicality/uniqueness of B is unnecessary, so the theorem applies in
particular to any prescribed canonical B satisfying the source bound.

The canonical-TI restriction has now been eliminated. Existing QIC full
vector spreading gives irreducibility from C1 at any length, including zero.
The existing PerronGauge API supplies an actual unital tensor B0, nonzero
scalar ζ and invertible X with B0_i = ζ X A_i X^-1. C1 propagates to every
longer length by transporting to the unital tensor and back. Amplified X
and geometric ζ factors normalize the derived window solution while
retaining the original window and coefficient spaces. No spectral,
canonical or normalization premise is added to the final theorem.

The actual nonzero length-N state derives a nonzero letter, and the actual
OBC representation derives positive virtual dimension. The final actual
state corollary therefore needs only the supplied C1 representation, source
size regime, actual bounded OBC tensor, coefficient equality and nonzero
physical state. There is no extra positive-C1-length condition. This writes
the prescribed-window existence direction. The known false claim that every
algebraic solution represents the prescribed state is unchanged and remains
corrected by the same-state/root-phase converse in #10381.

The source canonical OBC conditions now remove the remaining common-bound
premise as well. OBCCanonicalPhysicalRanks derives the actual prefix Gram
from the given faithful density recursion, derives the suffix Gram identity
from row normalization, and proves every original bond dimension equals its
physical cut rank. Faithfulness at the right scalar endpoint derives actual
state nonvanishing. QuadraticCanonicalOBCWindow reuses the existing periodic
cut-rank bound to derive D², changes only the common bound, and applies the
actual prescribed-window supplier. The rectangular tensor and dependent
virtual-path coefficient sum are retained definitionally; a public entry
identity displays the original supplied site matrix. The final theorem
therefore uses the source's canonical equations and actual coefficient
equality without a supplied D² bound or nonzero-state hypothesis.

Both the constructed canonical factors and the original given factors use
the shared PhysicalCutGramRecurrences identities. Their four forward/backward
Gram proofs have been refactored onto the same physical extension lemmas,
rather than copying the double-sum calculation into another representation.

All new Blueprint entries are notready. Source synchronization, imports,
mathematical roles, reader-facing prose, TeX formatting, file-size, tactic
scan, integrity and full-branch whitespace checks are used. No local Lean,
Lake, compilation, checkdecls or cache mutation; hosted acceptance and
integration remain pending. Issue #6089 remains open.
