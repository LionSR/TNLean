# Actual intrinsic blocking parity for #7111

Source: arXiv:1703.09188, `PropChiral`, lines 1209–1252, and
`prop:sigma1-and-sigma2-equal`, lines 1633–1733. The canonical intermediate
presentation restriction is explicit and recorded in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`. The final intrinsic
parity theorem derives this representative internally and has no canonical
input assumption.

This child combines the verified canonical even-family virtual comparison
from #10315 with the actual intrinsic twisted-transfer identity and weighted
nilpotent elimination from #10385. It introduces no similarity, stabilization,
source-factor, blocked-gate, or local-certificate witness among the hypotheses.

For the actual product tensor, `T = normalizedDiagonal (mulTensor U U)` in
product bond coordinates. The derived even-family comparison is
`U♯ = η z U z†`, with `η ∈ {1,-1}`. Unitarity and `η²=1` recover
`U = η z† U♯ z`, so direct product-tensor contraction gives
`T = η (z† ⊗ 1) E (z ⊗ 1)` for the actual normalized completely positive
transfer `E`. The proof identifies `E` using the existing physical-adjoint
double-layer formula and its explicit product-coordinate reindexing. No
bond-factor swap is silently inserted.

Existing MPU stabilization internally supplies the stabilized rank-one
transfer data, treating bond dimension one by its existing separate theorem.
Unitary conjugation transports the commuting exchange weight. The generic
weighted nilpotent lemma then removes the transient contribution at every
positive power, giving derived constants `η,C` with
`τ(U)=η C` and `τ(blockTensor U k)=η^k C` for every positive `k`.
The two parity identities follow from `η²=1`: odd blocking gives `τ(U)`, even
blocking gives `τ(blockTensor U 2)`.

The proof retains `C`. It never identifies the virtual sign with the first
intrinsic value, asserts `C=1`, or claims `τ_k=τ_1^k`. It also needs no
simplicity hypothesis beyond its explicit canonical MPU presentation for
these intrinsic numerical identities. It does not construct the source's
printed blocked gates or their sequential unwinding. The unrestricted source
proposition remains `notready`, and #7111 remains open.

New source is `MPS/MPU/CanonicalTwistedTransfer.lean`, with four public
statements and matching scope-specific `notready` Blueprint anchors. Native
validation covers pinned API review, generated imports, local import graph,
declaration coverage, mathematical roles, prose, TeX formatting, tactic scan,
source width/integrity, and diff checks. No local Lean/Lake command was run;
new proofs are source-written and uncompiled. Existing green parent evidence
is not evidence for these new declarations.

## Removal of the canonical input hypothesis

`IntrinsicBlockingParity.lean` now removes the canonical assumption from the
intrinsic parity theorem. The only inputs are positive physical and bond
dimensions, `IsMPU U`, and actual adjoint symmetry at every even length greater
than one. The existing reduced representative supplies a canonical `V` with
the same physical operator at every positive length. That exact equality also
derives `V`'s even-chain adjoint symmetry.

The physical trace argument in the existing supplied-standard-form
representative-independence theorem is promoted at its original owner as
`intrinsicTimeReversalSign_eq_of_mpo_two_eq`, and the old theorem now calls it.
The exact blocked-MPO reindexing then gives intrinsic trace equality at every
positive blocking length, from the actual original length-`2k` operator.
There is no equality at length zero and no bond-space or factor-choice
identification. The canonical odd/even identities transfer back to `U`.

The final public `IsMPU.intrinsic_blocking_trace_parity` has no CFII,
full-support, simplicity, source-factor, local-certificate, similarity or
spectral stabilization premise. All such data used internally are derived.
It is an unrestricted intrinsic numerical parity statement on actual MPU
families. It does not construct the source's prescribed blocked gates, and
it does not assert the two initial values equal or identify a virtual phase
with the first trace. The original source proposition remains `notready`.

This adds three public declarations (one promoted at the existing intrinsic
owner) to the four canonical declarations, for seven new public declarations
in this child. All seven have scope-matching `notready` anchors. The old
supplied trace-independence proof is refactored to reuse the promoted
physical-matrix argument; its changed proof bytes are not covered by the
historical green parent job. The same source-only validation boundary applies.
