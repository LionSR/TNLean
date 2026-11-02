# Finite Euclidean extension by zero

Mathlib supplies the actual extension-by-zero linear map and finite sum along
an injection. `Function.Embedding.euclideanExtendByZero` combines those APIs
with `LinearMap.withLpMap` to obtain a bundled complex Euclidean linear isometry.
The coordinate identities are the existing injective extension and outside-range
zero identities. No new configuration record or embedding structure is defined.

The same isometry applies directly to the standard dependent configuration
embedding `Function.Embedding.piCongrRight`. It is used for varying physical
alphabets and for their actual two-site boundary ranges and local parent terms.
This generic owner can also be consumed independently of the OBC reconstruction.

Relevant Mathlib sources were read at manifest revision
c55e6e786f49471c72fbddbec5415808896aec1e. No Lean, Lake, elaboration or build was
run. The source-written construction and its shared Blueprint entry remain
notready pending hosted validation. Native import, role, declaration-sync,
reader-prose, proof-integrity, width and whitespace checks are required.
