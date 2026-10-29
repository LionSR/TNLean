# Quadratic solution over the prescribed OBC window

Source: PGVWC07, arXiv:quant-ph/0608197, MPSarchive.tex lines 1139–1169.
This child stacks the actual OBC prefix-factor source from draft #10370 and
the physical cut-window construction from draft #10381. The unpublished
dependencies are actual Git ancestry, not imports presented as main APIs.

The supplied tensor B is an actual OBC representation of the prescribed
length-N vector of a canonical C1 TI tensor A. Its common bond bound is D²,
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

The TI tensor A remains explicitly canonical and C1. The source's printed
first clause assumes existence of a C1 TI representation; composition with
canonical normalization of that representation remains necessary before
claiming exactly that unrestricted input statement. The known false claim
that every algebraic solution represents the prescribed state is unchanged
and remains corrected by the same-state/root-phase converse in #10381.

All new Blueprint entries are notready. Source synchronization, imports,
mathematical roles, reader-facing prose, TeX formatting, file-size, tactic
scan, integrity and full-branch whitespace checks are used. No local Lean,
Lake, compilation, checkdecls or cache mutation; hosted acceptance and
integration remain pending. Issue #6089 remains open.
