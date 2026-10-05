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

The theorem identifies the actual open-region image as a vector space. It
does not assert a normalized reduced-density formula, isometric normalization
of the physical boundary map, flatness, entropy, arbitrary-region geometry,
or parent-Hamiltonian kernel completeness. The corresponding scope note
remains open for these additional source assertions. No gauging construction
is changed.

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

## Verification

- Exact isolated compilation with all four package options passed the
  extracted foundations, native rectangle geometry, actual support,
  witness/image/dimension and physical column-action modules.
- The physical matrix transport to the exact monomial formula passed a
  narrow proof probe using the existing spin-flip/exponent definitions.
  The final production MPO import/bridge remains for exact-head full CI.
- Strict regression tests pass with warnings-as-errors: one-site image
  dimension 16, a two-site rectangle meeting both seams with dimension 64,
  a forbidden native boundary column, a physical controlled-phase entry
  equal to −1, and guarded standard-only axiom audits.
- An independent read-only source/mathematical review found no theorem gap.
  Its sole documentation correction on order/normalization was applied.
- No new axioms, proof holes, heartbeat increases, or Mathlib source builds
  were used. Reused artifacts were source/trace/dependency audited.

The PR must retain explicit pending status for the production MPO bridge
until its exact-head full-root CI result is known.

The final publication audit checked all 23 open PR file lists successfully,
including the shared CZX chapter and scope note, with no overlap. After
merging main `b46e0aab`, every mathematical source in the audited local core
closure remained unchanged; only four module headers differed.
The revised standalone note compiles to three pages without undefined
references or overfull boxes; all pages were visually inspected.

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
seam-crossing rank 64, nonzero trace for a maximal proper rectangle, and guarded
standard-only axiom audits. No proof heartbeat limit was raised.
