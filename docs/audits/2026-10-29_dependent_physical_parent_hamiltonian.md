# Actual parent transport on dependent physical configurations

Source: PGVWC07, `Papers/quant-ph_0608197/MPSarchive.tex`, Theorem 9 and proof,
lines 1195–1220. Arbitrary consecutive blocking gives potentially different
finite physical spaces at different sites.

`DependentPairCoordinates.lean` composes Mathlib's existing dependent product
splitting twice. It separates two chosen physical coordinates in order and
retains the actual dependent outside coordinates. The coordinate bijection
commutes pointwise with all site embeddings. Its Euclidean reindexing also
commutes with extension by zero: both constructions preserve coefficients in
the image and vanish outside it. No common physical alphabet is assumed.

`VaryingPhysicalParentHamiltonian.lean` defines the actual local interaction as
the complementary rectangular pair-range projection, extended by identity on
the true outside space and conjugated by that coordinate bijection. Its open
sum is over all adjacent bonds. It proves positivity of the actual local terms
and full sum. The previously derived actual local-projector transport then
gives full Hamiltonian intertwining under arbitrary site embeddings and exact
zero-kernel equivalence on embedded vectors. The argument assumes neither C1
nor canonical row normalization, and has no supplied local annihilation,
projector identity or Hamiltonian transport premise.

This is a genuine extension of the parent construction to dependent physical
spaces, with no duplicate chain record or parallel source predicate. The
uniform reconstruction theorem is preserved unchanged. The remaining bridge
identifies the common-alphabet specialization of these local terms with the
existing uniform coefficient-section parent model, then transports its actual
state line and normalization. Until that bridge is derived, this continuation
does not claim the full varying-physical uniqueness theorem or close the
source scope note. The short-length source convention is separate.

No Lean, Lake, elaboration or build was run. All new Blueprint entries and
proofs remain notready. Native validation covers generated imports, mathematical
roles, full declaration-sync and duplicate tags, reader-facing prose, proof
integrity, width and whitespace. The proofs reuse pinned Mathlib dependent
splittings, coordinate isometries and projection positivity, and the shared
physical extension/spectator transport owners rather than copied geometry.
