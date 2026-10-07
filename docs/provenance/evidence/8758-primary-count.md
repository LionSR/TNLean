# The number of primary identifiers in an actual layer

Four original declarations in `PrimaryCounting.lean` define the finite set
of actual primary pitch indices, prove its exact membership criterion, and
bound its cardinality by the coarse-cell count and physical cut boundary.
Write D_k for the dyadic layer and U_j for the open pitch interior. An index
j belongs to the finite set precisely when D_k ∩ U_j is nonempty. This
characterization holds at all nonnegative scales, with arbitrary translated
origins and integer shifts.

Private finite candidate rectangles are obtained from the pitch indices of
the lower and upper corners of each retained coarse cell. Every actual
intersection supplies an index in the corresponding rectangle, so the finite
candidate construction loses no primary. If the coarse index k is at most
the pitch index p, each candidate rectangle has at most four indices. Thus

\[
|\mathcal P_k|\le4|I_k|.
\]

For the cut-endpoint set of a finite square-lattice domain and region, the
existing coarse-cell count then gives

\[
|\mathcal P_k|\le32(2C_0+1)^2\,|\partial_\Lambda A|.
\]

The bound is uniform in the domain, cut, origin and selected shifts, including
empty domains, cuts and layers. Its coefficient depends on the fixed
neighborhood radius. The index ordering is explicit in the general-scale
result and is intrinsic to the manuscript's rounded scales.

## Source and mathematical scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
The primary construction is in lines 212–218, and the per-layer count is in
lines 237–238 in the proof of `prop:two-families`, immediately before
`geometry:primary-pieces`. The proofs are independently written; no upstream
Lean source or proof text is reused.

The new count concerns all actual primary identifiers in one layer. The
closed-fragment decomposition and individual primary diameter and separation
are the earlier `PrimaryRegions.lean` and `PrimaryFragments.lean` results.
The affine mesh and contacts, isolated stars, simultaneous repairs,
descendant counts, birth separation from earlier actual regions, the full
two-family partition and both manuscript headline theorems remain open.
Independent mathematical review approved this four-declaration scope.

## Exact source and canonical local evidence

Exact verified source: `b1dc393c764962cbc0cfb4c1bbefd3519c04a967`.
The four declarations are:

- `TNLean.PEPS.AreaLaw.Geometry.primaryPitchIndices`;
- `TNLean.PEPS.AreaLaw.Geometry.mem_primaryPitchIndices_iff`;
- `TNLean.PEPS.AreaLaw.Geometry.card_primaryPitchIndices_le`;
- `TNLean.PEPS.AreaLaw.Geometry.card_primaryPitchIndices_boundary_le`.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Targeted Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | 0 | 16.557 |
| Imported-declaration audit | `lake env lean docs/provenance/evidence/8758-primary-count-axioms.lean` | 0 | 4.032 |

`PrimaryCounting` compiled in 9.9 seconds, and the Geometry aggregator in
3.7 seconds, without warnings. The imported audit prints all four exact
public names. Every reported dependency is one of `propext`,
`Classical.choice` and `Quot.sound`. No placeholder, extra axiom or prohibited
proof mechanism is reported.

Both commands ran consecutively through the own-worktree
`scripts/lake_build_locked.sh --` under the shared repository lock, using
the warmed cache and pinned prebuilt Mathlib artifacts. No local full-library
or Mathlib source build was repeated. The separate preparation worktree had
no `.lake` directory and performed no cache or build operation.

Evidence log paths and SHA256 hashes:

- `8758-primary-count-build.log`: `cb141f53c2671ee9c3efbbc7d4c4120087014bb677fa5bcccac1f56db89674c9`;
- `8758-primary-count-axioms.log`: `9707040cc097434ddf36e51e5011d70416e4c8d668519bd478bc6528834ae742`.

Each log records its actual command, exact source revision, elapsed time and
exit code. Only trailing whitespace is removed from captured output; the
actual build diagnostics and quoted axiom output are preserved.

## Provenance and integration

Complete current-policy source/license/notice and provenance validation
passes all 209 entries. The new promotion changes only the four rows in
`docs/provenance/openai-math.d/8758-primary-count.json`. The previous 205
entries, including the seventeen parent declarations' completed evidence,
retain their exact bytes. The promoted source, imported audit, log hashes
and exact axiom names are checked against the frozen source revision.

Strict non-mutating elaboration with the package options passed in 4.035
seconds before canonical integration. Independent mathematical and source
review passed. Complete blueprint source synchronization against the
manifest-identical warmed QICLean sources passed; those sources were read
without mutation, and the preparation worktree needed no dependency cache.
All four new declaration tags, prose checks and formatter idempotence were
checked. Generated imports are current: 75 aggregators cover 2,833
production modules.

The parent contribution recorded a local whole-library compiled-blueprint
failure caused by the missing pre-existing `Fibonacci.olean` artifact. Its
failure log and record are preserved. That unrelated check was not repeated
for this changed-leaf contribution. Complete compiled blueprint checking and
rendering are left to the separate full-library CI build; no successful
compiled-blueprint or full CI outcome is claimed in this local evidence.
