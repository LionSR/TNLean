# Simultaneous OBC Schmidt canonical form

Source: PGVWC07, arXiv:quant-ph/0608197, Theorem thm:OBC-Vidal,
lines 431–458, and freedom theorem free-OBC, lines 461–486, in
Papers/quant-ph_0608197/MPSarchive.tex.

Current main already proves actual OBC existence for every nonzero state of
positive length, with the exact physical cut ranks and the bound d^(floor N/2).
CutRank also supplies a one-sided isometric representation. The present
change adds the simultaneous equations from conditions 1–3 of Theorem 1;
it does not reprove raw OBC existence.

At every interior physical cut, the existing compact SVD supplies weighted
left singular vectors V†D as a basis of the actual coefficient column space.
Their Gram is D² with strictly positive diagonal entries, and the actual
suffix-coordinate factor is U with UU† = I. The endpoint cut bases are fixed
to 1 and the actual normalized physical state, retaining its complex phase.
The existing minimalCutChain reconstructs that state exactly from those bases.
Exact physical configuration bijections turn its prefix and suffix recurrences
into the density propagation and right-canonical equations. Trace preservation
then gives unit trace at every cut.

The main statement OBCChainTensor.exists_canonical_coeff_eq takes only positive
chain length and a normalized physical state. Nonvanishing of the state and
positivity of the physical dimension are derived. Its conclusion supplies the
actual chain, its exact Schmidt cut ranks, both canonical equations, both unit
endpoint densities, and positive definite diagonal unit-trace densities at all
bonds. No density family, canonical form, square gauge, or full-rank surrogate
is an input. Normalization is the source's state convention, also necessary
for its printed endpoint and trace conditions; the open chain has positive
length.

The rectangular freedom theorem is also source-written. Actual original
prefix and suffix products factor the physical cut matrix through the
original virtual bond. Therefore the physical cut basis columns lift through
the original prefix P_k: choose Z_k with P_k Z_k = F_k. Basis independence
supplies a left inverse T_k F_k = I. Defining Y_k = T_k P_k gives Y_k Z_k = I;
the actual adjacent-prefix recurrences prove A_k^i = Y_k B_k^i Z_(k+1).
The initial Y and final Z are the scalar endpoint identifications. The
canonical construction retains its chosen physical cut bases internally,
so this comparison applies to that very same canonical chain, without
assuming density, rank equality, or an invertible square gauge.

The additional public theorem
OBCChainTensor.exists_canonical_coeff_eq_rectangular_maps takes only an
original representation of positive length and normalization of its actual
coefficient state. It returns the actual simultaneous canonical chain and
all its densities together with these rectangular maps. Thus both source
Theorem 1 and Theorem 2 now have complete written proof bodies; this is
not a hosted-verification or integration claim.

All proof bodies are source-written without placeholders or bypasses.
Independent mathematical review found the weighted-basis orientation and
both Gram equations consistent. Native source synchronization, generated
imports, mathematical-role checks, prose, formatting, tactic scan, module-size
and whitespace checks are used. No local Lean invocation, build, checkdecls
or cache mutation. Every new Blueprint entry remains notready pending hosted
verification; the issue remains open for verification and integration of both
source theorems.
