# Corrected same-state quadratic reconstruction converse

Source: PGVWC07, arXiv:quant-ph/0608197, system (S) and Theorem 8,
MPSarchive.tex lines 1139–1176. The finite-ring phase and endpoint-cut
corrections are documented in the two existing paper-gap notes.

Current main already proves weighted fixed-length uniqueness, including
unitary conjugacy up to an Nth-root phase. It also constructs every endpoint
and internal cut from condition C1 and actual fixed-length equality. The
quadratic-system module itself only supplied internal comparison data;
there was no theorem consuming an actual system solution to prove the
corrected same-state reconstruction converse.

The new converse consumes an actual QuadraticReconstructionSolution over a
supplied window, a PGVWC07 canonical tensor A satisfying C1 at L0, the full
cut regime N > 2*L0 + D^4, actual equality of the two nonzero length-N vectors,
and no canonical or injectivity condition on the candidate solution tensor B.
Its row normalization is already one of the quadratic equations. Canonical
C1 reduces A to one weighted block. Applying weighted uniqueness against
B's unit row normalization derives weight(A) = 1, a unitary U and ξ with
norm one and ξ^N = 1, satisfying A_i = ξ U B_i U†.

QuadraticSolutionRephasing constructs an actual solution of the same system
with Bhat_i = ξ B_i, Yhat_j = ξ^(-j) Y_j and Zhat_j = ξ^(j+1) Z_j. These scalar
factors preserve every internal inversion and multiply every site equation
by ξ; unit modulus preserves normalization. The Nth-root condition preserves
the actual length-N vector. The converse therefore returns an actual rephased
solution with exact GaugeEquiv to A, through the same actual unitary U. It
also exposes the existing UnitGaugePhaseEquiv predicate before rephasing.
Mathlib's Unitary.toUnits supplies the matrix-ring unit directly; no separate
matrix-inverse construction is duplicated.

This is a bounded partial delivery for #6089. The source theorem's existence
clause still needs an actual supplier of the displayed doubled-bond window
and its quadratic gauges from the unique OBC canonical form and the given
C1 TI representation. The independent OBC canonical existence draft does not
automatically identify that window. No window identity, endpoint chain or
solution is assumed to replace this missing source argument. No assertion
that every algebraic solution represents the prescribed state, or that all
solutions have been classified, is introduced. The original full source
Blueprint theorem remains notready; the new explicitly bounded same-state
lemmas are separate and also notready.

Native source synchronization, gap-note declaration extraction, generated
imports, mathematical roles, reader-facing prose, TeX formatting, tactic
scan, file-size, integrity and whitespace checks are used. No local Lean
invocation, build, checkdecls or cache mutation. Hosted verification and
integration remain pending, and #6089 remains open.
