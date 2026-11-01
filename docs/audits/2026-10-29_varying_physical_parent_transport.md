# Physical transport for differently sized open-chain blocks

Source: PGVWC07, `Papers/quant-ph_0608197/MPSarchive.tex`, Theorem 9 and proof,
lines 1195–1220. Consecutive blocks may have unequal physical dimensions.
The existing full-chain candidate has one common physical alphabet, so its
scope note remains open. This continuation derives actual physical transport
identities rather than silently treating unequal physical spaces as equal.

The generic owner `Algebra/EuclideanExtendByZero.lean` uses Mathlib's actual
extension-by-zero linear map and finite injection sum. It defines a bundled
Euclidean linear isometry, with exact coefficient preservation and zero outside
its image. Mathlib's dependent product embedding applies it to the full physical
configuration space. A common alphabet of dimension sum_i d_i and each site's
injection into it are constructed from finiteness; no dimension-bound premise,
positive-size side premise, or new chain record is introduced.

`PhysicalAlphabetEmbedding.lean` derives preservation of the actual rectangular
span and canonical row sum. It uses the existing extension by zero for each
site matrix. For independent physical embeddings on the two sites, the actual
trace-boundary range is exactly the isometric image of the original range.
Mathlib's `LinearIsometry.map_starProjection` then intertwines the actual
complementary parent projectors, with no supplied projector identity.

`PhysicalAlphabetLocalTerms.lean` consumes that derived identity and the existing
canonical `ContinuousLinearMap.rightFiberwiseMap` identity extension. It proves
that the actual extended local parent term intertwines under independent
embeddings of both active alphabets and the full outside configuration space.
The outside coordinates may themselves be dependent configurations. No supplied
support, local-kernel, full-chain reconstruction, or Hamiltonian transport
conclusion appears as a premise.

The remaining assembly identifies each dependent full-chain configuration space
with its actual pair/outside coordinates, makes these identifications commute
with the physical embeddings, and sums the local intertwining identities. This
must be connected to the existing uniform-alphabet kernel/reconstruction theorem
before a full varying-physical-dimension uniqueness result is claimed. This
continuation does not assert that final theorem or change the source scope note
to complete. The short-length convention remains a separate source-context task.

Pinned Mathlib sources were scouted first. The coordinate and projection proofs
reuse its extension, dependent embedding, finite sum, range composition and
isometric-projection APIs. Source-independent review found no concrete mismatch
in the isometry, span, row sum, pair range or pair projection arguments. No Lean,
Lake, elaboration or build was run; all new entries remain notready. Native
checks cover generated imports, mathematical roles, declaration ownership and
sync, reader-facing prose, proof integrity, width and whitespace.
