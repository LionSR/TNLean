# Actual canonical intrinsic blocking parity for #7111

Source: arXiv:1703.09188, `PropChiral`, lines 1209–1252, and
`prop:sigma1-and-sigma2-equal`, lines 1633–1733. The supplied canonical
presentation restriction is explicit and recorded in
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

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
