# Native semi-regular parent completion

## Source-facing result

`IsGInjective.torusParentKernel_eq_commutingClosureSpan_of_isSemiRegular`
identifies the **entire actual positive plaquette-parent kernel** with the
span of the actual native commuting closure vectors. Its dimension is
`Nat.card (CommutingPairConjugacyClass G)` by
`IsGInjective.finrank_torusParentKernel_of_isSemiRegular`.

Inputs are an arbitrary finite-dimensional unitary semi-regular matrix
representation `U`, arbitrary native physical coefficients `a`, and source
G-injectivity `IsGInjective (torusLegRep U) (siteMap a)`. The irreducible
blocks, their actual positive multiplicities, canonical local G-injectivity,
and both parent supports are derived. There is no ground-state expansion,
local-range equivalence, or parent-kernel identity among the hypotheses.

Source: `Papers/1001.3807/paper_v3.tex`, Definition 4.5 (1010–1013),
Definition 5.1 (1278–1296), Theorems 5.7/5.9 and closure classification
(1440–1621), seam movement (1622–1647), and Section 7 (2977–3019).

## Exact remaining scope restrictions

- Both native periods are at least three. This is the existing finite-simple-
  graph restriction, not a proof of the smaller-period/multigraph cases.
- The native closure capstones use one site tensor `a` repeated at every vertex.
  The oriented graph transport itself permits vertex-dependent physical tensors.
- A single arbitrary semi-regular `U` is used on all native edges. The paper's
  explicitly allowed link-dependent representations (1310–1316) are separate.
- These are linear parent-space/kernel equivalences, sometimes involving
  positive nonunitary physical filters. No equality of spectra, spectral gaps,
  or local-unitary equivalence is claimed.
- Unitarity is part of the source's definition of semi-regularity.

See `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex` and
`docs/paper-gaps/rmp_peps_examples_small_torus.tex`. The source-facing modules
carry the required explicit scope-restriction markers.

## Proof chain

1. Arbitrary edge-flip flags describe actual native tails. Open contraction
   formulas retain every virtual boundary coefficient, including both crossing
   orientations. Their span is proved equal to `regionGroundSpace`.
2. The copy map is unchanged by flipping an edge because it commutes with
   simultaneous head/tail swaps. Reversed internal factors are transposed
   block matrices. Both matching-sector and target product-range supports
   follow from the actual internal slices and edge-covering parent regions.
3. Fourier coordinate transport uses `Q.map star` on reversed edges. A literal
   pair-swap identity, actual all-boundary covariance, and exterior matrix
   blocks prove local and full parent transport. Coisometry is derived at 1.
4. Positive multiplicity weights move to invertible sitewise physical filters.
   The previously derived block factory therefore handles the actual arbitrary
   multiplicities of `U`, then the dimension multiplicities of the regular
   representation. The fixed-representation physical comparison handles
   arbitrary G-injective physical tensors.
5. `torusNativeEdgeFlip` points horizontal bonds right and vertical bonds down,
   including the wraparound seams. The native tails are exactly right/down,
   and `graphOrientedIncidentMatrix_torus` equals `torusLegMatrix U` in actual
   top/right/down/left coordinates. The numbered local tensor G-injectivity
   bridge is explicit. Degree four and native plaquette edge/vertex coverage
   are proved geometry, not supplied comparison hypotheses.
6. A separately constructed native regular averaging site permits application
   of the already merged regular parent dimension theorem. This yields the
   full arbitrary semi-regular native parent dimension.
7. Generic inserted graph contractions with identity internal insertions have
   every regional physical slice in the original actual range. Boundary and
   exterior insertions are absorbed into arbitrary boundary coefficients.
   Native/ordered matrix transposes are explicit. Existing arbitrary-U seam
   movement places commuting seams outside every internal plaquette edge,
   including period three. This proves actual closure membership using only
   local invariance, with no semi-regularity assumption at that step.
8. The existing semi-regular commuting-class closure independence gives the
   same finite dimension. Membership and equality of dimensions force the
   actual closure span to exhaust the full parent kernel.

## Validation and dependency provenance

All twenty new production modules and their changed TNLean dependency closure
compile with `-j1`, `pp.unicode.fun=true`, `relaxedAutoImplicit=false`,
`weak.linter.mathlibStandardSet=true`, and `maxSynthPendingDepth=3`.
Three strict regressions use those options plus `warningAsError=true`, with
axiom output guarded against exactly `propext`, `Classical.choice`, and
`Quot.sound`:

- `TNLeanTest/OrientedSemiRegularParentTransport.lean`
- `TNLeanTest/TorusSemiRegularParentDimension.lean`
- `TNLeanTest/TorusSemiRegularParentGroundSpace.lean`

They exercise reversed-edge copy multiplicity 3 versus block dimension 2,
the arbitrary native incidence API, exact full-kernel spanning, and a concrete
3×3 torus with two copies of the trivial group's one-dimensional irrep.

The eight regular capstone proof sources were byte-verified against published
main `f3d3bade1f56b87f88fc8a87314bf451591483b7`, then rebuilt read-only from the
integration worktree into this worker's private validation outputs. This also
rechecks their use of the previously generalized rectangular physical-map
API. No shared artifact was changed. Exact QIC dependency is
`2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`; no Mathlib rebuild was performed.

The exact new production-file and public-declaration inventory is in
`2026-10-05_native_semiregular_parent_declarations.md` (20 modules, 140 named
public declarations). Shared root imports and blueprint routers were not edited.

## Safe later consolidation

The ordered proof tower can become a false-orientation specialization, but
first separate the low-level common definitions to avoid import cycles:

1. Move orientation-independent finite incidence products, regional physical
   coordinate equivalences, and numbered virtual/physical coefficient
   equivalences into neutral foundational modules. Currently the oriented
   modules import their older ordered containers.
2. Move ordered-recovery lemmas into a bridge importing both constructions.
   Then the generic oriented open-contraction core need not import old
   `GraphOpenBondFactors` or the ordered regional-range proof.
3. Specialize `GraphOpenCopyTransport`, `CopyCanonicalLocalTransport`, and
   `CopyCanonicalParentTransport` at `o = false`; retain every old public name.
4. Specialize ordered Fourier local/parent transport at false orientation and
   retain its existing map/equivalence APIs. Keep the useful per-edge matrix
   family block/product algebra as the shared implementation.
5. After extracting their neutral coordinate definitions, make ordered
   G-injectivity and physical-copy-weight theorems false-orientation wrappers.
   The arbitrary-representation factories are already shared; the final
   ordered capstones can then be short specializations.

This is a follow-up refactor, not part of the validated source-completion
packet. The native inserted-closure membership and final dimension/spanning
modules remain independent consequences and should be retained.
