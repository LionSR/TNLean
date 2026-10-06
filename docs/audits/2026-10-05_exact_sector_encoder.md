# Exact coherent sector encoders

This batch adds a fixed-width factorization and a genuine linear-depth
compiler for the complete canonical sector encoder. It supplies the exact
branch of the all-accuracy theorem in `CoherentGroundspaceConversion`; this
audit records the algebraic factorization and its ownership.

## Simplification and ownership

The elementary coordinate embeddings, weighted block sum, nonempty-word,
periodic-vector and blocked-physical-matrix identities now live in
`MPS/Core/BlockSum`. Their declaration names are unchanged. Their former
bodies are removed from `OrthogonalBlockSum`; `blockPairs` and its membership
identity are removed from `OverlappingBlockInjectivity`. The current-main
`Preparation/BondEmbedding` module also reuses the ten pure coordinate/pair
embedding declarations from this core module, retaining its density and
square-root helpers. `OrthogonalBlockSum` obtains the core declarations
through that preparation import; `OverlappingBlockInjectivity` imports
the core module directly. Fully qualified names, binders and the ten proof
bodies are preserved, with no Core-to-Preparation dependency. The
nonempty-word induction now expands finite matrix sums
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
listed QIC and unchanged TN prerequisite companions are collected under
separate size caps, with exact source, dependency, toolchain and byte hashes.
The new conversion targets are checked before the mandatory full root build.
Failure to export or download is not a proof pass.

## Production verification checkpoint

At commit `b41285d27567aabb58a4558ee70d4854ee2a02e4`, PR CI run
`37383154425`, build job `112009921098`, passed the early Lake build of
all seven coherent targets. This includes `CoherentGroundspaceConversion`
and `SectorEncoderGroundspace` with their actual imports and repository
options. The latter retains the range hypothesis `3 * D ^ 5 ≤ L ≤ N`
and positive physical and bond dimensions. The full root build, reverse
dependencies, direct regressions and declaration checks remain separate
required gates; the early-target pass is not a full-repository pass.

The resolved scope note concerns explicitly matched canonical encodings.
It does not validate unrestricted chosen-vector conversion or erase the
source-claim obstruction recorded by the compatible-seed gap note.
