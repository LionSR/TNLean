# Template depth rows: proof status and remaining argument

This is the geometric slice of [#8754](https://github.com/LionSR/TNLean/issues/8754),
on `codex/area-law-template-rows`, stacked on the model PR
[#8788](https://github.com/LionSR/TNLean/pull/8788) at
`158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2`. The model files are unchanged.
The source is Lemma 9.4 of the September 24, 2026 area-law manuscript,
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/08-scanner.tex`,
lines 571–629. All new proof text is original; none is copied or adapted from
upstream Lean code.

## Implemented statements

`Geometry/TemplateRows.lean` derives horizontal interval rows directly from
`TemplatePolygon.region` and `Template.mem_sample`. Compactness gives attained
real endpoints, and exact sampling gives their ceiling/floor interval, even if
that interval is empty. It also gives the actual dilation row-window formula,
subadditivity of layer cardinalities over arbitrary unions, and
`template_card_le`: for `Ctpl ≥ 1`, `T.points.card ≤ 9*n*s₀`.

These statements do **not** yet prove the depth-layer estimate. In particular,
horizontal interval sections alone do not imply that dilated rows are intervals.
The allowed slopes are essential for the missing step. No desired regularity
property or cardinality estimate has been inserted into the model.

## Remaining mathematical argument

The following calculation explains a conservative candidate constant **24**. It is an
informal proof plan, not an elaborated Lean theorem or a completed source label.

1. Express the actual convex hull of each allowed rectangle or triangle as the
   intersection of the closed half-planes of its sides. Horizontal sides bound
   the row index. Each other side gives a lower or upper affine bound on the
   horizontal coordinate with slope −1, 0, or 1. There is at least one bound
   of each kind because the polygon is bounded.
2. Round the lower intercepts upward and upper intercepts downward. Integer
   row shifts commute with rounding, including at negative coordinates.
   Thus the sampled endpoints are a maximum of lower affine functions and a
   minimum of upper affine functions. Their difference is convex, so the
   nonempty integer rows form an interval. Both endpoints are 1-Lipschitz on
   this interval. Neighboring row intervals overlap or are adjacent, including
   for a thin diagonal sample consisting of singleton rows.
3. If the sample is empty, every dilation is empty. Otherwise, radius-r dilation
   takes each row from the union of the original row intervals in the window
   of distance r, extended horizontally by r. The adjacency above makes this
   union an integer interval. Its endpoints are the sliding minimum and maximum
   of the original endpoints, minus or plus r. Compare radius j and radius j−1
   directly on an old output row: its window gains at most one original row at
   each end. Original endpoint 1-Lipschitz bounds therefore change each sliding
   extremum by at most one; the additional horizontal extension adds one more.
   No separate 1-Lipschitz theorem for dilated endpoints is needed for this count.
4. The proved `sample_subset_box` gives coordinate widths at most 2s₀ about any
   sampled point. There are at most 2s₀+2j−1 old output rows, each acquiring at
   most two sites at either endpoint.
   There are exactly two additional extreme rows, each of length at most
   2s₀+2j+1. Consequently the single-piece new layer has size at most

       4(2s₀+2j−1) + 2(2s₀+2j+1) = 12s₀+12j−2 ≤ 24s₀−2

   when 1≤j≤s₀. Bounding this by 24(s₀+1), summing over the pieces using the
   proved union reduction, and applying the template scale would give the
   desired estimate for every Ctpl≥24.

The first three steps, the formal counting in step 4, and their assembly from
the model remain to be implemented. In particular, the compact-section
ceil/floor theorem already implemented does not assert that these real
endpoints have the required slope formulas. Empty samples, overlaps and
disconnected unions require no removal or disjointness assumption in the
proved reduction.

An explicit formulation of the missing polygon identity uses the four linear
forms `x`, `y`, `x+y`, and `x−y`. For each such form f, let m_f and M_f be its
minimum and maximum over the actual vertices. The identity to derive is

    P = {p : m_f ≤ f(p) ≤ M_f for all four forms f}.

Each side of an allowed polygon has one of these forms as its normal, but
that observation still needs a proof from the convex-hull constructors.
Once established, the sampled row bounds are explicitly

    ceil(m_y) ≤ y ≤ floor(M_y),
    max(ceil(m_x), ceil(m_(x+y))−y, ceil(m_(x−y))+y) ≤ x,
    x ≤ min(floor(M_x), floor(M_(x+y))−y, floor(M_(x−y))+y).

These formulas isolate the missing convex-hull argument from the subsequent
integer maximum/minimum and sliding-window proofs. They are not assumed by
any exported theorem in this draft.

For the constructor-specific reverse inclusion, a triangle can be treated with
determinant-based barycentric coordinates α,β satisfying α≥0, β≥0 and α+β≤1.
A rectangle uses its two orthogonal side coordinates with 0≤α,β≤1. This avoids
requiring a general polytope representation library. These are proof plans from
independent review, not validated additional Lean results.

More explicitly, write `cross(u,v)=u₁v₂−u₂v₁`. For a triangle put
`D=cross(b−a,c−a)`, which the constructor proves nonzero, and use

    α = cross(p−a,c−a)/D,
    β = cross(b−a,p−a)/D,
    γ = cross(c−b,p−b)/D.

Algebra gives α+β+γ=1 and p=γa+αb+βc. Each numerator is an oriented
side functional whose values at the three vertices are 0,0,D. Its normal
is a scalar multiple of one of the four forms above. The four range bounds
therefore put each numerator between min(0,D) and max(0,D). Splitting on
the sign of D gives α,β,γ≥0, hence convex-hull membership. This also explains
why a proof must preserve the sign of D rather than presume an orientation.

For a rectangle use α=((p−a)·u)/(u·u) and β=((p−a)·v)/(v·v).
Nonzero orthogonal u,v give positive denominators and
p=a+αu+βv. The allowed directions make each dot functional a scalar
multiple of one of the four forms. Its vertex range gives 0≤α,β≤1.
The four convex weights are (1−α)(1−β), α(1−β), αβ and (1−α)β.
These formulas specify the missing reverse inclusion; they are still
unformalized, and are not used as hypotheses in the Lean declarations.

## Validation

The pinned Lean release was installed from its official release asset.
`lake exe cache get` was attempted before any library build, with a writable
`XDG_CACHE_HOME`. Cache downloads failed with HTTP 403; the missing
`Mathlib.olean` guard prevented a local library build. Only the cache retrieval
executable was built, not Mathlib proof sources. Normal PR CI is the required
fallback. `TNLeanTest/TemplateRows.lean` is registered in that workflow with
strict options, warnings as errors, and axiom output.

No entropy, edge-boundary, repaired-family, or physical area-law theorem is
claimed. OpenAI Codex (GPT-6) assisted the original proofs and documentation;
maintainer mathematical review is pending.
