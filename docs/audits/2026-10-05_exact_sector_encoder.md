# Exact coherent sector encoders

This batch adds a fixed-width factorization and a genuine linear-depth
compiler for the complete canonical sector encoder. It remains a stage toward
the all-accuracy logarithmic-depth theorem described in the scope note.

## Simplification and ownership

The elementary coordinate embeddings, weighted block sum, nonempty-word,
periodic-vector and blocked-physical-matrix identities now live in
`MPS/Core/BlockSum`. Their declaration names are unchanged. Their former
bodies are removed from `OrthogonalBlockSum`; `blockPairs` and its membership
identity are removed from `OverlappingBlockInjectivity`. Both import the
core module. The nonempty-word induction now expands finite matrix sums
directly instead of obtaining elementary multiplication through a polar
uniqueness import. No analytic result is duplicated or moved into Circuit.

The exact construction uses a full virtual space of dimension D squared,
rather than a new enumeration of supported coordinates. The existing polar
support projector supplies both the Gram identity and support of the virtual
encoder. Supported injectivity itself proves independence of the periodic
sector columns, removing an otherwise redundant rank hypothesis.

Generic polar and operator-norm identities reuse Mathlib and QICLean. The
new trace-selector and cyclic-pair identities mention MPS data and remain in
TNLean. The actual-ring support compiler is consumed from the non-normal
capstone; it is a genuine unitary theorem, separate from its measurement
consumer. Blueprint ownership places its tag beside the simultaneous unitary
sector theorem.

## Validation scope

The core extraction and exact encoder are checked against actual imports
using source-matched warm artifacts and the pinned Lean and QICLean versions.
The complete affected reverse closure and declaration checks remain CI gates.
The exporter is optional build-artifact engineering: only the explicitly
listed QIC compiled companions are collected, with exact source, pin,
toolchain and byte hashes. Failure to export or download is not a proof pass.
