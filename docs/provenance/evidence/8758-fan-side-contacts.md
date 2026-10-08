# Boundary contacts of actual fan triangles

The two original records have passed exact-source canonical verification
and independent mathematical review.
The complete direct package-option source check and independent mathematical
review also passed at the released hash below.

The completed parent is the combined fan-contact and primary-cover contribution
at evidence `a4833852f7e6dbee5930b1c983fff39e3a74daa7`, with verified proof
`26dbf77709501643284144f4294c4d768966958b`. Its immutable baseline measures
all 282 records and all 128 tracked files recursively beneath
`docs/provenance/evidence`. Every parent shard, entry, historical file, policy,
license and dependency pin is preserved. The completed parent is draft
[#8897](https://github.com/LionSR/TNLean/pull/8897).

## Mathematical statements

Fix an arbitrary origin o, a natural dyadic exponent ℓ, a signed cell index z
and an arbitrary optional midpoint choice for each side. Each fan triangle is
the convex hull of the actual cell center and the endpoints of one resulting
perimeter segment. Its intersection with any whole side of its own closed
square equals the intersection of its perimeter segment with that side.
The equality includes empty intersections and contacts consisting of one point.
There is no supporting-face premise or positive-contact assumption.

For two distinct indexed actual fine cells in the same layer construction,
the intersection of a reference fan triangle with the other closed square
equals the intersection of its perimeter segment with that closed square.
The origin, finite endpoint set, layers and natural dilation width are
arbitrary. The reference midpoint mask is arbitrary. No late-scale bound,
positive-width condition, nonempty-endpoint assumption, matching certificate
or condition that the contact contain two distinct points is imposed.
Actual fine-cell membership and distinct indexed cells are the only
geometric hypotheses in this second statement.

A fan triangle is the convex join of its center and its perimeter segment.
The center lies in the open cell interior and the perimeter segment lies in
the closed cell. Convexity places every point outside the perimeter segment
in the open interior. An own square side is disjoint from this interior.
Distinct actual half-open fine cells are disjoint; because the reference
interior is open, it is also disjoint from the closure of the opposing cell.
These two exclusions give both intersection equalities. Existing endpoint
geometry, convex-join identities and the actual fine-cell disjointness theorem
are reused; no supporting-line or four-side coordinate proof is repeated.

## Manuscript and independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, lines 299–323, at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The manuscript path is
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
The two results are separately scoped geometric ingredients for the cited
construction; they do not mark the full two-family proposition as proved.
Original proofs were written from the manuscript mathematics. No upstream
Lean source or proof text is reused. OpenAI Codex (GPT-6) assistance is
identified separately from attribution.

The public assignment is
[#8758, comment 6049135316](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6049135316).
The original notice IDs are
`8758-tnlean.peps.arealaw.geometry.cell_fan_polygon_side` and
`8758-tnlean.peps.arealaw.geometry.fine_layer_fan_cell_contact`.

## Released source and independent review

| Module | Public declarations | Released SHA-256 | Direct check |
| --- | --- | --- | --- |
| `FanSideContacts.lean` | `cellFanPolygon_inter_dyadicCellSide`; `fineLayer_cellFanPolygon_inter_closedCell_eq` | `1a818c1ab1d6528e11ff7fd784c4357b4d275d4cb0bd29284f0c1be0256fc402` | Exit 0, no diagnostics; real 4.68 s, user 2.37 s, system 2.79 s |

Independent complete mathematical review approves both strong statements and
the exact released hash. This hash precedes original-notice insertion; the
subsequent five-file source freeze includes the installed module and imported report.
The direct check is not a canonical build or imported kernel report.

## Exact-source canonical verification

Frozen source: `9dce097b1d70dff4a59a8a3ed0fb035c725166ac`. Completed parent evidence:
`a4833852f7e6dbee5930b1c983fff39e3a74daa7`, with verified proof
`26dbf77709501643284144f4294c4d768966958b`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 16.396 s | `31921284c7ce73608783583f7fca8fdadad375c1638fac80d19dfae5a76a3a4d` |
| Imported two-name report | `lake env lean docs/provenance/evidence/8758-fan-side-contacts-axioms.lean` | Passed, exit 0 | 5.230 s | `506b458f4923559ca8ddb89a391028f6661393781227643ba4cdf6743248c207` |

Both raw logs retain exact revision, command, elapsed-time and exit-code
headers and contain no diagnostics. The imported report contains exactly two
quoted declarations, each depending only on propext, Classical.choice and
Quot.sound. The production module, Geometry aggregator, report, mathematical
chapter and parent chapter retain all five frozen byte sequences.

Strict promotion and the unchanged normal policy pass all 284 records.
Exactly two original rows are added. All 282 parent records and shards,
and all 128 tracked historical evidence files, remain unchanged; no old
declaration is reverified. Only the two new rows' historical preparation
descriptions clarify that canonical verification was pending before source
freeze. The finalizer compares raw promotion to the committed planned rows
and requires its finalized output to equal the normal-policy production shard.
All policy, license, dependency and toolchain bytes are unchanged.

Source synchronization passes with `total_blueprint_refs = 20232` and
20,238 lines in `blueprint/lean_decls`, complete reverse coverage and no
missing, stale or duplicate references. Generated imports cover
2,857 production modules in
75 files. The scoped chapter contains two
theorems and two proofs, with four completion markers. Independent review,
formatter idempotence, reader prose, module guards and pattern checks pass.
The approved pre-notice direct check remains 4.68 seconds wall, 2.37 seconds
user and 2.79 seconds system time; its released SHA-256 is retained above.

Full CI and compiled book checking remain separate. The historical local
whole-library declaration check encountered missing
`TNLean/MPS/Examples/Fibonacci.olean`; that prior evidence and limitation
remain unchanged. QICLean stays pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

## Further geometric obligations

A shared nondegenerate segment with the closed dummy neighborhood still needs
its own whole-base containment argument. Consistent global interfaces and
identifiers, the initial-star construction, recursive repairs, descendants,
the full two-family proposition and both headline PEPS/area-law theorems
remain further obligations. This contribution proves the two stated boundary
intersection equalities only.
