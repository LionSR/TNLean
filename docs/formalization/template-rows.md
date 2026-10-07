# Template depth rows

This is the geometric slice of [#8754](https://github.com/LionSR/TNLean/issues/8754),
on `codex/area-law-template-rows`, stacked on the model PR
[#8788](https://github.com/LionSR/TNLean/pull/8788) at
`158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2`. The model files are unchanged.
The source is Lemma 9.4 of the September 24, 2026 area-law manuscript,
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/08-scanner.tex`,
lines 571–629. All new proof text is original; none is copied or adapted from
upstream Lean code.

## Implemented argument and validation status

The compiled theorem `Geometry.template_layer_card_le` states that, for an
actual `Template Ctpl n s₀`, `Ctpl ≥ 24` and `1 ≤ j ≤ s₀` imply

    (ambientDilation T.points j \ ambientDilation T.points (j - 1)).card ≤ n.

It adds no row regularity, cardinality, connectedness, or disjointness hypothesis.
The supporting code is split into four modules:

- `TemplateRows.lean`: compact horizontal sections of actual convex hulls,
  ceiling/floor descriptions of exact samples, ambient dilation identities,
  union-layer subadditivity, and `template_card_le`, which proves
  `T.points.card ≤ 9*n*s₀` for `Ctpl ≥ 1`.
- `TemplatePolygons.lean`: supporting slabs derived from the actual triangle
  and rectangle constructors, reduced to four linear forms.
- `TemplateRowBounds.lean`: rounded integer row profiles, consecutive occupied
  rows and windowed columns, and transport between adjacent occupied rows.
- `TemplateLayers.lean`: horizontal intervals after dilation, endpoint extension
  by at most two per radius step, the single-piece layer count, and the scale
  argument for arbitrary unions.

All four production modules and the full library build passed at
`ada3ccb6dfe231695676953030a4333d36997f8c` in
[PR CI run 37616454111](https://github.com/LionSR/TNLean/actions/runs/37616454111).
The strict actual-model regression, all 42 axiom audits, style lint, compiled
blueprint declaration checks, full blueprint job, and compilation-time checks
also passed. Every export depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The observed outputs are now guarded in the regression file.

Evidence is preserved in
[the build log](../provenance/evidence/8754-layer-build.log),
[the strict regression and axiom output](../provenance/evidence/8754-layer-axioms.log),
and [the blueprint log](../provenance/evidence/8754-layer-blueprint.log).
All 42 provenance entries record this revision and evidence hashes. The earlier
23-export evidence remains explicitly scoped to its earlier revision.

## Mathematical derivation

For each actual polygon, take the minimum and maximum of each of the forms
`x`, `y`, `x+y`, and `x−y` over its vertices. The convex hull is exactly the
intersection of these four closed strips. Forward containment follows from
convexity. For reverse containment, the implementation constructs nonnegative
barycentric weights directly from the triangle sides, or four convex weights
from the rectangle's orthogonal side coordinates. It handles either sign of
the triangle determinant and does not assume an orientation.

Exact lattice sampling rounds the real lower bounds upward and the upper
bounds downward. Write the resulting integer bounds as `lx, ux, ly, uy, ls,
us, ld, ud`. Row `y` is empty outside `ly ≤ y ≤ uy`; inside that vertical strip
it is the possibly empty integer interval with endpoints

    L(y) = max(lx, ls−y, ld+y),
    U(y) = min(ux, us−y, ud+y).

These formulas work at negative coordinates and when a polygon samples no
lattice point. They imply consecutive occupied rows and endpoint motion at
most one between adjacent occupied rows. Applying the same inequalities after
restricting to a vertical window gives consecutive occupied columns. This
also handles a thin diagonal with only one sampled point on each row.

The row of an ambient radius-r integer dilation is the horizontal extension
by r of the original sample in the vertical window `[y−r,y+r]`. Consecutive
occupied columns make this extended row an interval. When the radius grows
from r to r+1, a new source point can be moved into the old nonempty window
with horizontal displacement at most one. Increasing the horizontal radius
adds one more unit. Thus each endpoint of an old nonempty output row extends
by at most two, and that row acquires at most four sites.

For a nonempty sample, `sample_subset_box` bounds its coordinate widths by
2s₀ about any sampled point. At depth j there are at most `2s₀+2j−1` old rows
and two additional extreme rows, each of length at most `2s₀+2j+1`. Therefore

    4(2s₀+2j−1) + 2(2s₀+2j+1) = 12s₀+12j−2 ≤ 24(s₀+1)

for `1 ≤ j ≤ s₀`. An empty sample has empty dilations and contributes zero.
Union-layer subadditivity sums this bound over all pieces, allowing overlaps
and disconnected unions. The actual template scale field and `Ctpl ≥ 24`
then give the requested bound by n.

## Validation procedure and scope

The pinned Lean release was installed from its official release asset.
`lake exe cache get` was attempted before any library build, with a writable
`XDG_CACHE_HOME`. Cache downloads failed with HTTP 403; the missing
`Mathlib.olean` guard prevented a local library build. Only the cache retrieval
executable was built, not Mathlib proof sources. Normal PR CI is the required
fallback. `TNLeanTest/TemplateRows.lean` is registered in that workflow with
strict options, warnings as errors, actual-model examples, and axiom audits
for all 42 exported declarations.

No entropy, edge-boundary, repaired-family, or physical area-law theorem is
claimed. This advances only the geometric slice of #8754. OpenAI Codex (GPT-6)
assisted the original proofs and documentation; maintainer mathematical review
is pending.
