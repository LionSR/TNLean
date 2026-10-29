# Shared identity-extension transport under physical embeddings

The actual fiberwise identity extension is owned by Martingale/SpectatorMaps.
The Euclidean coordinate extension by zero is owned by Algebra/EuclideanExtendByZero.
`ContinuousLinearMap.rightFiberwiseMap_extendByZero` combines these two existing
constructions: an active intertwining H E = E G induces the corresponding
identity-extended intertwining on active and outside coordinates.

The proof observes that a fiber at an embedded spectator is the embedding of
its source fiber, and a fiber outside that image is zero. It handles empty
coordinate spaces without added nonempty assumptions. The active intertwining
is a hypothesis of this generic transport theorem; the actual parent and
physical-sector callers derive it from their actual subspace projections.

The known parent caller in PhysicalAlphabetLocalTerms is refactored separately
so the shared owner commit can be consumed by independent physical-sector
work without depending on the OBC implementation. The public generic theorem
is anchored once in the shared parent-Hamiltonian chapter.

No Lean, Lake, elaboration or build was run. Native source/import/role/sync,
reader-prose, proof-integrity and whitespace checks are required, and the
shared Blueprint entry remains notready pending hosted validation.
