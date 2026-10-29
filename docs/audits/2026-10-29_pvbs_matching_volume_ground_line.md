# Matching-volume pure particle ground line

This continuation uses the existing PVBS one-particle vector and the existing
pure-window interaction and periodic Hamiltonian. No parallel vector,
Hamiltonian, zero-momentum predicate, or all-volume premise is introduced.
The source context is the finite-prefix investigation for SPWC10, Theorem 5;
the coefficient input is the PVBS construction, arXiv:1112.4097, Section II.

For every positive range R and q^R=1, the actual matching-volume periodic
Hamiltonian has kernel exactly the span of the existing PVBS particle vector.
The vector is nonzero because its first-excitation coefficient is one, and
its Hamiltonian equation is derived. The one-step coefficient identity is
q times the rotated vector equals the original vector. Thus translation acts
by q inverse, and the existing Fin.cyclic_induction/additive translation law
derive line invariance at every offset, without replacing line invariance
by exact vector invariance.

At a full-length window, cyclicCfg is exactly translation by the negative
starting offset. Its actual coefficient sections therefore lie in the same
particle line, proving annihilation by every pure-window projector. Conversely,
the positive-sum kernel characterization and the full-window zero-offset
section put every Hamiltonian kernel vector in that line.

For q≠1, an actual matching-volume kernel vector fixed by every cyclic
translation must vanish: the exact kernel identity reduces it to c times the
particle vector, and a nonzero c would make that vector invariant, contrary
to the retained one-step phase. This proves absence of nonzero zero-momentum
ground vectors in this matching volume. It does not assert an all-volume
Hamiltonian model or a counterexample to an unrestricted source theorem.

Independent mathematical/API review found no concrete mismatch in the full
window offset, finite cyclic induction, scalar cancellation, kernel span or
nonvanishing steps. Pinned APIs include Fin.val_sub, finRotate_apply,
Fin.cyclic_induction, cyclicTranslateState_add and the actual interaction
section kernel theorem. No local Lean, Lake, elaboration or build was run.
All five public declarations and their Blueprint entries remain notready.
