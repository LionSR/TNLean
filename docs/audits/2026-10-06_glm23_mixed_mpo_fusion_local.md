# GLM23 actual mixed-MPO fusion: local source audit

## Dependency scope

This work starts from the local merge of mixed-action commit
`313fb03e2661aa26696cd20c83d9d7ff9400e6bb` and cross-transport commit
`3f962d3fc0fff0704df76d16d2b468b7782900c5`. Both parents have identical
`lean-toolchain` and `lake-manifest.json` contents. Their SHA-256 values are,
respectively, `bc84812c94489d1e3e191baa1dc10d5eb684382d7fe9d2a5ab085e72c1c67e47`
and `a6ccb46404b164ab38d9c250f613bd902794d6e94436677764c7b610b7b82b18`.
The sole merge conflict was the additive CI regression list; both parents'
examples were preserved. No new router, blueprint, or workflow entries are
part of this initial source deliverable. Nothing is published by this work.

## Mathematical content

The two endpoint families use common labels `a : Fin r`, fusion multiplicities
`N a b c`, and one-state action multiplicities `m a`. Endpoint physical spaces
are square bond spaces; their dimensions may differ. The endpoint state
blocks are positive-dimensional and injective. Fusion and action maps are
actual exact biorthogonal decompositions.

`MixedEndpointMPOFusionMaps` defines mixed fusion analysis and synthesis with
three independent bond dimensions at each endpoint. Only incoming pairs
`(inl α, inl β)` and `(inr α, inr β)` survive. Output dimensions in the
analysis-synthesis product may also differ, as needed for orthogonality
between different target labels. No identity on the full incoming bond is
used.

`BoundaryActionCrossFusionEntries` specializes the checked rectangular
cross-endpoint action-tree contraction to a matrix unit, then reorders the
finite scalar sums into the physical operator-product contraction. The
existing `BoundaryActionTreeEntries` controls the associator ordering.

`MixedEndpointMPOFusion` uses endpoint fusion for physical sectors 00 and 11,
and the cross-endpoint formula and its endpoint reversal for sectors 01 and
10. Physical-sector zeros are eliminated before virtual sectors are split.
It constructs an actual `IsBiorthogonalDecomposition` of the mixed product
into mixed labelled target tensors with explicit maps. The family-wise
arbitrary-boundary formula uses the existing blockwise boundary transport
result. The periodic formula uses the existing constructor of
`IsMPOFusionAlgebra` from exact biorthogonal decompositions. It does not apply
the single-target `IsBoundaryClosed` criterion to a general labelled family.

## Source interpretation and remaining scope

The source is the pinned arXiv:2203.12563v3, `REsubmission.tex`, lines
1667–1685, together with `fusiontensors`, `eq:orthoW`, `fusiontensors2`,
`eq:orthoV`, and the actual L orientation in `rawrels`, `eq:F_symbol2`, and
`1Fsymbol`, lines 491–552.

Equality of the selected endpoints' actual raw L matrices is an explicit
already-aligned hypothesis. The equal-L cross contraction needs no inverse
L, common F, MPO injectivity, ambient completeness, or nonzero multiplicity.
Common F concerns coherent recoupling and is not needed for the exact local
fusion identity established here. This result is not the full source claim
that the mixed construction is an injective representation of the same
fusion category.

Deriving raw equality from gauge-class equality, mixed MPO injectivity,
actual mixed L inheritance, coherent F inheritance, physical adjoint
closure, Hamiltonian symmetry, and the full phase classification are not
proved here.

## Validation status at the integration snapshot

The complete combined probe 2 finished on 2026-10-06 at 01:20:35 UTC with
exit 1 after 1386 wall seconds under the shared build load. The entire
`MixedEndpointMPOFusionMaps` module, its regression file, and all four map
axiom guards passed. Their checked source SHA-256 values are:

- Maps: `8b459b2e2b41c88071cae06f817956393f3e633f0ca6577334bee93ad7ad3a4d`
- Map tests: `60e51d9e12c66b0f46b4c0b3d343fe162c3d3ecc94df17d96d390f2d80f28033`

The same run reported finite-sum ordering failures in the scalar cross
entry and missing normalization steps in the fusion assembly. The five
cross/fusion axiom guards correctly rejected the resulting failed proofs.
The integration snapshot repairs these issues by deterministic, staged
sum distribution with typed sum-congruence steps; explicit matrix
association before entry expansion; and explicit product/equivalence
coordinate reductions. These repaired bytes have not yet passed a
complete Lean check. No heartbeat, recursion, timing, or axiom guard was
weakened. This snapshot is not a verified full-fusion result.

The focused check concatenates only modules whose exact source bodies are
supplied, including the unchanged cross-transport helper and
`BoundaryMultiplicity`, whose compiled artifacts are absent from the
canonical warmed import tree. It uses one Lean process and one thread,
the strict package flags, and no output artifact options. The imported
mixed-MPO constructor and action-L/tree-entry sources match the canonical
source hashes. The unchanged action module is not imported or edited.
This is not a standalone module build, router check, or CI timing result.

Regression sources exercise independent input/output dimensions,
rectangular analysis-synthesis products, unmatched-sector zeros,
cross-corner sandwiches, and the endpoint-exchanged actual decomposition.
The nine standard-axiom guards cover the four fusion-map lemmas,
cross-sector entry, full reconstruction, biorthogonality, arbitrary
boundaries, and periodic fusion. Four guards passed; five remain pending
on the repaired proof snapshot.

A scoped tactic-pattern scan found no repeated patterns at the repository
thresholds. Static whitespace, line-length, and proof-integrity checks pass.
Independent read-only review found no mathematical issue in the L
orientation, reversed sector, independent dimensions, or labelled
boundary formula.

## Draft integration checkpoint, 2026-10-06 01:28 UTC

The integrated draft combines the exact checked dependency trees of PRs
#8695 (`785d0144839811ea5cabd5f89dc06417b8b19961`) and #8711
(`85bf15e3147a84e2f9940675064f75a3ef79e063`). The latter includes #8691.
This stacked dependency code is reused, not counted as newly proved fusion
code. The new package has four production modules (816 lines), three strict
regressions with thirteen standard-axiom guards, and seventeen uniquely
owned blueprint declaration references. Eight guards have passed combined
checks for the exact cross-transport and fusion-map snapshots; the five
cross-entry/fusion guards and repaired complete assembly remain pending.
There are no checked markers on this package's new blueprint entries.

Independent source review confirmed the two raw-L relations, endpoint
reversal, rectangular fusion-map dimensions, and the boundary orientation
`V productBoundary(X,Y) W`. It does not replace Lean elaboration.

The six new Tenkz panels passed native production-wrapper and hard-signature
checks. Exact fixtures cover 972 mixed letters, twelve crossed trees,
1,524 boundary words, 1,524 periodic words, and 625 rectangular sandwich
entries; eleven deliberate source/coefficient mutations are rejected.
The focused strict web build and visually reviewed ten-page PDF passed,
with no final PDF warnings or overflow. Local browser layout is unrun;
the real fail-closed browser gate remains in CI.

Existing workflow lists receive the three regressions and the fusion diagram
commands. The full chapter browser fixture now counts all seven two-picture
rows: one original action comparison, one reused mixed-state interpolation,
two reused mixed-action rows, and three new fusion rows. No existing gate
is weakened. Source/reverse reference synchronization, unique ownership,
generated imports, module-size/numbering, prose, Python/YAML and whitespace
checks pass. Exact-head full Lean, guarded regressions, timing, and complete
blueprint/browser verification are pending the draft's CI run.
