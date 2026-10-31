# Exact finite norm contraction of the uncle trial

The actual five-segment trial has squared norm equal to the real operator
trace of the composition of its five transfer maps. The wall transfers use
exactly the existing single-wall word sums as rectangular Kraus matrices.
They evaluate at the identity to the already-defined one-wall Gram matrix.

The source trial on 6N+1 sites has lengths N, N+1, 2N-1, N+1, N. Its two
exterior A segments join under the operator trace, leaving the separations
2N and 2N-1 and moving intervals of length N+1. The exact configuration
transport is supplied by the existing trial-coordinate lemmas; no alternative
trial or modified wall interval is introduced.

The proof factors finite rectangular Kraus compositions, expands their
operator trace in matrix units, and reindexes the actual coefficient sum.
It works with zero bond dimensions and empty general-trial segments. Only the
source's numbered-segment specialization requires N positive.

This is the finite input to the remaining norm asymptotic in arXiv:1210.6613,
proof of Lemma lowenergystates, lines 1196–1265. The next argument must replace
the two actual transfer powers by their primitive rank-one limits with a
quantitative error, and compare the surviving product of actual one-wall
weights with the source norm. The finite identity assumes none of these
estimates and does not assert quadratic norm growth or gaplessness.

Validation: independent mathematical review of the Kraus product and trace
orientations; exact finite scalar checks including the N=1 source intervals
and empty-segment cases; source import, declaration, prose, and diff checks.
No local Lean build or elaboration was run. New Blueprint results remain
pending validation.
