# Actual CZX rectangle boundary

Issue: #8040. Source: Chen, Liu and Wen, arXiv:1106.4752, boundary discussion
at source lines 330–345 and 377–385; review arXiv:2011.12127, Appendix A,
CZX tensor and printed boundary matrices at 2502–2518 and 2582–2605.

## Physical result

For a positive proper bounded coordinate rectangle in a torus with both
periods at least three, the actual open-region contraction has exactly one
independent effective qubit per boundary plaquette. Its image has dimension
`2 ^ (2 * w + 2 * h)`. The region's physical CZX symmetry acts in those
faithful coordinates by flipping every effective spin with the cyclic
nearest-neighbor controlled-phase sign.

The proof uses the existing `openRegionMap`, whose sum contains only bonds
touching the region. It does not substitute an abstract boundary tensor or
assume support, injectivity, a Gram identity, or a local inverse.

- Native clockwise crossing bonds are enumerated using actual torus edges;
  the existing rectangle crossing-cardinality theorem supplies surjectivity.
- Nonzero physical coefficients determine all incident labels uniquely.
  Each coefficient is zero or one, and distinct boundary columns have
  disjoint physical supports.
- The eight side/corner transitions force the cyclic adjacent-pair condition.
- Arbitrary boundary bits extend from distinct torus plaquette corners.
  Copying them to physical qubits gives exact coefficient selectors, proving
  injectivity and the image dimension.
- Physical on-site maps commute with actual contraction. Internal controlled
  phases occur twice and cancel; crossing phases remain once.
- The printed review MPO differs from `X^P D_P` by `(-1)^P`; the perimeter
  is even, so the final physical intertwiner has no residual sign.

The normalized bra-ket display is not substituted for the printed matrices.
The standalone scope note also corrects its previous arbitrary-length
conflation of `X^N D_N` with `D_N X^N`.

## Scope retained

The theorems identify the actual open-region image and the support and rank
of the actual reduced density, including after trace normalization. They do
not assert the source's explicit density formula or nonzero eigenvalues,
isometric normalization of the physical boundary map, flatness, entropy,
arbitrary-region geometry, or parent-Hamiltonian kernel completeness. The
corresponding scope note remains open for these additional source assertions.
No gauging construction is changed.

The coordinate intervals satisfy `xStart + w ≤ width` and
`yStart + h ≤ height`. Their endpoints may lie on a coordinate seam, and
their crossing bonds may wrap through that seam. A region whose coordinate
interval itself wraps around the torus is outside this statement.

## Reuse and dependency extraction

Four existing declaration/proof blocks were moved byte-for-byte, with all
public names preserved and old imports re-exporting them:

1. Local CZX on-site symmetry and pull-through into `CZXOnSiteSymmetry`.
2. The four basic cyclic-boundary declarations into `CZXBoundaryChain`.
3. Native incident-coordinate uniqueness from `RegularTorusEntropy` into
   `TorusIncidentCoordinates`.
4. The four-leg enumeration/equivalence from `TorusSingletonRegion` into
   the same geometric owner.

An exact block comparison against `adb7e1751` passed. These are existing
PEPS-specific declarations, not a new generic algebra API. The fresh open-PR
filename audit found no overlap; `TorusRectangleBoundaryCard`, the active
prerequisite surface, was reused unchanged.

The new on-site module has 10 non-Mathlib dependencies; the incident-coordinate
module has 7. The complete new rectangle core has 70 (67 TNLean, 3 QICLean),
with no whole-Mathlib or Brouwer import. The former on-site owner included 369
non-Mathlib modules through its MPO imports. These are structural closure
counts, not a claimed controlled timing benchmark. The final printed-MPO
consumer still uses its existing broad library dependencies.

## Initial verification

- Exact isolated compilation with all four package options passed the
  extracted foundations, native rectangle geometry, actual support,
  witness/image/dimension and physical column-action modules.
- The physical matrix transport to the exact monomial formula passed a
  narrow proof probe using the existing spin-flip/exponent definitions.
  The production MPO import/bridge was subsequently checked by the full CI
  run recorded below.
- Strict regression tests pass with warnings-as-errors: one-site image
  dimension 16, a two-site rectangle meeting both seams with dimension 64,
  a forbidden native boundary column, a physical controlled-phase entry
  equal to −1, and guarded standard-only axiom audits.
- An independent read-only source/mathematical review found no theorem gap.
  Its sole documentation correction on order/normalization was applied.
- No new axioms, proof holes, heartbeat increases, or Mathlib source builds
  were used. Reused artifacts were source/trace/dependency audited.

The final publication audit checked all 23 open PR file lists successfully,
including the shared CZX chapter and scope note, with no overlap. After
merging main `b46e0aab`, every mathematical source in the audited local core
closure remained unchanged; only four module headers differed.
The initial standalone note compiled to three pages without undefined
references or overfull boxes; all pages were visually inspected before the
subsequent reduced-density extension.

## Actual reduced-density support extension

The subsequent rectangle extension uses the existing actual closed-state cut
factorization and reduced-density definition. Global plaquette witnesses select
one native crossing assignment on the complement, so every effective column is
literally a closed-state physical slice. The reduced-density range equals the
cut-matrix range; together with generic support containment this proves equality
with the open-region image and rank `2^(2*w+2*h)`. Its nonzero trace follows from
positive semidefiniteness and positive rank. Trace normalization preserves the
same support and rank, without asserting flatness, entropy, or an isometric
normalization of the effective boundary map.

The existing plaquette extension argument is factored into one public witness;
the original selector reuses it. Independent source review checked actual
complement-edge identification, coefficient one (not only proportionality),
proper rectangle and seam conditions, and the absence of a parent-kernel
hypothesis. Both source modules pass individual full-option isolated compilation.
Strict regression tests include actual one-site rank 16, trace-normalized
rank 64 for a rectangle meeting both seams, nonzero trace for a maximal proper
rectangle, and guarded standard-only axiom audits. No proof heartbeat limit
was raised.

## Independent integration review, 2026-10-05

At head `bdbc87a228ae1a37a90b208bfeb932cdf509ae90`,
[PR CI 37248153606](https://github.com/LionSR/TNLean/actions/runs/37248153606)
checked synthetic merge `d33c25632e6a257bc4023298f72d824dfabab77e` against
main `a639b63df363ff0b9c0db1c17d75424fee97881d`. All feature Lean source
bytes in that synthetic merge equal the reviewed head. The root build
completed all 12,133 jobs, including the printed-MPO bridge and migrated
regular-PEPS consumers. The strict physical tests, declaration checks,
compilation-time gates and blueprint checks passed. Import completeness and
the demolition guard passed independently.

The review checked the source boundary discussion, actual incident-label
uniqueness, all side/corner transitions, coefficient-one selectors, the
complement-cut argument, trace normalization and the printed operator order.
No mathematical blocker was found within the explicit rectangle scope.

The author then integrated main `9926c1d0a4ab71aeda7b7d3ea697ee6fc54e8f79`
in `b2eb48a39819adda95eb75f03275c2aef54f39e3`, preserving both the
`HalfChainSpectrum` and `CZXRectangleBoundary` strict test entries. The scope
clarifications following that integration change documentation only; they
preserve every feature definition and proof. The earlier green run is not
claimed as exact-head validation of a later commit.
