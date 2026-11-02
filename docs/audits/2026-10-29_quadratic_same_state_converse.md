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

The existence direction now also has actual physical source-written ingredients.
InjectivePeriodicCuts factors the physical cut matrix through the virtual cut
vectors, derives a suffix right inverse, proves equality of physical and virtual
prefix column spaces, constructs their basis, and proves exact rank D². C1
propagates along a positively weighted canonical tensor by removing its weight
inside the proof. Every endpoint-inclusive reconstruction-window cut therefore
has rank D² in the source size regime.

PeriodicCutBasisCoordinates transports this basis to the actual site subsets
and proves that actual coordinate slicing has matrix A_i tensor I. In
QuadraticPhysicalCutWindow, arbitrary actual physical cut bases define the
window by the existing cutSlice maps. Changes of basis supply the two gauges;
the identities of linear maps prove both the local and inverse equations.
Geometric factors remove the positive canonical weight to normalize the
solution tensor. The window is proved equal to the existing cutSiteMatrix
family after its justified coordinate reindexing. No window gauges, rank
identity or quadratic solution is an input.

This remains a partial delivery for #6089 until the canonical OBC choice is
composed with this basis-independent window theorem and hosted validation is
complete. The separate OBC canonical existence draft exports the actual
canonical cut-basis choice; that unpublished supplier is not imported here as
if it were on main. No assertion that every algebraic solution represents the
prescribed state, or that all solutions have been classified, is introduced.
The original full source Blueprint theorem remains notready, as do the new
explicitly stated supporting results.

Native source synchronization, gap-note declaration extraction, generated
imports, mathematical roles, reader-facing prose, TeX formatting, tactic
scan, file-size, integrity and whitespace checks are used. No local Lean
invocation, build, checkdecls or cache mutation. Hosted verification and
integration remain pending, and #6089 remains open.
