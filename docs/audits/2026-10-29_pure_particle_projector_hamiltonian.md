# Pure particle projector Hamiltonian

Context: #10386 and draft #10405. This child supplies an actual Hamiltonian
component, not a full counterexample to SPWC10 Theorem 5.

The local operator is the orthogonal projection onto the complement of the
line of the existing `pvbsEdge q R`. It is positive. The implementation uses
the existing `periodicLocalInteractionES` and `periodicInteractionHamiltonianES`,
without replacing identity extensions by unnormalized compression sums.

The local-section equations are derived from actual local and global operator
equations. The generic spectator restriction reuses the existing finite-range
conjugacy of `periodicLocalInteractionES` inside a larger active interval.
No local kernel inclusion, section decomposition, or spectator annihilation
premise is assumed by the final theorem.

For q ≠ 0 and R ≥ 2, the two terms on the first R and last R sites of an
(R+1)-site interval have no common kernel. Their actual coefficient sections
are multiples of the same geometric particle vector; the previously written
nonzero first-cut minor gives the contradiction. Every M-site Hamiltonian
kernel vector with M ≥ R+1 has sections on such an interval killed by these
two terms, hence every section is zero. Thus the actual periodic Hamiltonian
has trivial kernel at every M ≥ R+1. In particular R=7 gives every M ≥ 8.

This result does not show that the same interaction has a nonzero momentum
ground state at M=R, nor does it construct the main or mixed physical sectors
of the candidate model. Those obligations, all-volume uniqueness of the full
model, and comparison with the precise source conventions remain separate.
The library's original PVBS parent operator, whose local space also contains
the vacuum, is not altered or confused with this pure-line interaction.

## Verification

No local Lean, Lake, build, elaboration or checkdecls is run, as requested.
All ten new declarations have supporting Blueprint entries marked `notready`.
The source uses exact pinned dependency APIs, not a floating checkout.
Native checks and bounded independent source review are recorded in the PR;
source-written proofs are not kernel acceptance.

Independent final source/API review found no concrete mismatch in the cyclic
section equation, projector kernel, endpoint coordinate identities, or actual
spectator conjugacy for every M ≥ R+1. Native import, role, synchronization,
TeX, file-size, integrity, pattern-scan and whitespace checks pass.
