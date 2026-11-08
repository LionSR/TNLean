# Finite-prefix completion and cyclic momentum

Source: SPWC10, arXiv:0909.5347, Theorem 5, lines 850–880.
Parent draft #10369 proves an actual eventual fixed-tensor alternative or
an explicit degree-five obstruction at every prime length. Its statement
and hypotheses are preserved in this child.

The printed constant-dimension branch has the natural quantifiers:
one common dimension K, with a possibly different tensor at each length.
It does not require one tensor to generate all the finitely many short
lengths as well as the eventual tail.

The raw OBC existence theorem on current main already constructs every
nonzero positive-length state with bound d^(floor N/2). The new
PeriodicFiniteRepresentation module composes it with the existing
site-independent cyclic-block construction. Every nonzero vector fixed
exactly by cyclic translation is therefore represented at size
N*d^(floor N/2), with its actual amplitude and phase. An OBC representation
or a finite periodic representation is not an input. Conversely the
existing periodic trace cyclicity proves that every periodic trace-MPS
vector is fixed exactly by those translations.

PeriodicBondPadding extends matrices by unused zero coordinates and proves
that positive-length vectors are unchanged. Consequently an eventual
bond-D tensor with threshold M0 supplies one actual common size
K = D + M0*d^M0 + 1 for all exactly cyclic-invariant ground vectors, including
the finite short prefix. Long lengths use the padded eventual tensor;
short lengths use the constructed finite representation and are then
padded. Uniqueness identifies the actual nonzero vector's entire ground
line.

FinitePrefixUniformBond also proves an exact equivalence: a common-size
nonzero ground family at every permitted positive volume exists if and
only if every permitted short positive volume M < M0 has a nonzero ground
vector of zero cyclic momentum. This is the precise remaining finite
condition, not a presumed short-MPS family. Uniqueness plus translation
symmetry gives a ground eigenline, which by itself does not say that its
cyclic eigenphase is one. No derivation of that short zero-momentum
condition from the complete global source hypotheses is asserted here,
and no counterexample to the source's complete hypotheses is claimed.

The earlier supplied-OBC scope note for PGVWC07 Theorem 3 is updated:
its raw existence step is already on main, and the composed actual
finite cyclic-invariant representation is now source-written. The fixed
length and exact vector invariance are explicit.

Independent mathematical and bounded pinned-API review found no concrete
mismatch. Native source synchronization, import aggregation, roles, prose,
TeX formatting, tactic scan, module size, integrity and whitespace checks
are used. No local Lean invocation, build, checkdecls or cache mutation.
All new Blueprint entries remain notready; hosted verification and
integration are pending. Issue #10280 stays open for the explicit finite
zero-momentum obligation as well as acceptance of the proof stack.
