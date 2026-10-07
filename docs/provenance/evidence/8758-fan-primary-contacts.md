# Fan contacts and the fine-cell cover of primary regions

These three local geometric prerequisites establish contacts within a cell
fan and the finite closed fine-cell decomposition of a primary birth region.
The exact source has passed canonical compilation, three kernel reports,
provenance validation and independent mathematical review.

Completed color parent: draft [#8895](https://github.com/LionSR/TNLean/pull/8895)
at `4aaa0256f74aa317cb0180856a9e2579c21b341e`, with verified proof
`acff16af5c9f4726de4efbee7eb01f56729e42b1`.
A new immutable baseline measures all 279 current records and all 124 tracked
files recursively beneath `docs/provenance/evidence`. It preserves every
parent shard, entry, historical file, policy, license and dependency pin.
Earlier preparation artifacts and baselines have not been replaced.

## Within-cell fan contacts

Fix an arbitrary origin o, natural scale ℓ, signed dyadic-cell index z and
optional side-midpoint mask. The actual triangles are the convex hulls of
the cell center and the endpoints of each resulting perimeter segment.
For two distinct slots, an intersection containing two distinct points
forces the perimeter segments to be consecutive. The triangle intersection
is exactly the radial segment from the actual center to their shared
endpoint. Endpoint adjacency is derived from contact.

For any two-color function on these slots, use the existing connected
components of the graph joining equal-colored triangles whose perimeter
segments have a common consecutive endpoint. Their regions are the unions
of the actual triangle regions in each component. If two distinct run
regions have an intersection containing two distinct points, every triangle
in one run has a different color from every triangle in the other.
The proof extracts an actual noncenter intersection point, identifies
contacting triangles, derives endpoint adjacency and uses color constancy
on the two components.

The statements are local to one cell. They have no layer-membership,
late-scale, dilation, sparsity or global coloring-certificate assumptions.
The two-color function is arbitrary. Global interface classification,
primary and run identifier assembly, isolated stars, recursive repairs and
the two-family proposition are further obligations.

## Fine-cell cover of a primary

For an arbitrary origin o, natural layer, fine and pitch indices k, ℓ, p,
finite endpoint set Z, natural width C, canonical residues
`a,b : Fin (2^(p−ℓ))` and signed pitch index J, assume only ℓ ≤ k and ℓ ≤ p.
Filter the actual fine-layer indices to those outside both belt residues
whose shifted pitch index is J. The primary birth region at J equals the
finite union of the closures of those actual fine cells.

The statement introduces no new public region or index. It includes empty
layers, non-retained primary identifiers, refinement depth zero, arbitrary
signed indices and disconnected primaries. When p = ℓ, every actual fine
cell is a belt cell and the open pitch interior is empty; both sides of the
equality are empty. No nonempty-endpoint, late-scale, positive-width,
retained-index or strict-pitch-depth assumption is added.

The existing nonbelt-cell containment supplies one inclusion. For the other,
choose the actual fine cell of a point in the layer–pitch intersection.
The strict pitch bounds force its shifted coordinate remainders into
`1 ≤ r < 2^(p−ℓ)`, so Euclidean integer division gives the exact signed pitch
quotient and excludes both belt residues. The finite union of the closed
squares is closed; taking the closure of the layer–pitch intersection gives
the reverse inclusion. Boundary points are included by closure, rather than
assigned to an open pitch region.

This equality supports later extraction of an actual cell witness from a
whole nondegenerate geometric segment. Two arbitrary points in a disconnected
intersection do not provide such a segment. Global primary/run interfaces,
consistent labels, sectors, isolated stars, repairs, descendants, the full
two-family proposition and both headline theorems remain separate obligations.

## Manuscript and independence

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `prop:two-families`, at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The manuscript path is
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
Triangle contacts cite lines 308–323, run contacts 313–323, and the primary
cover 212–218 and 299–323. The original notice IDs and module-specific
anchors are unchanged. No upstream Lean source or proof text is reused;
OpenAI Codex (GPT-6) assistance is disclosed separately from attribution.

The original public assignments are
[fan contacts](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048750510)
and [primary cover](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6048881242).
No future fan-side contact result is included.

## Released source and independent review

| Module | Public declarations | Released SHA-256 | Direct check |
| --- | --- | --- | --- |
| `FanRunContacts.lean` | `cellFanPolygons_nontrivial_inter_cases`; `cellFanRunRegions_contact_colors_ne` | `4a890d08930fe05e2b7f319d0fc9725937211a4d4db1385db7d8ef1845dd41ed` | Exit 0, no diagnostics; real 17.06 s, user 5.24 s, system 6.58 s |
| `PrimaryFineCellCover.lean` | `primaryBirthRegion_eq_iUnion_nonbeltCell_closure` | `a522974ecffdf40925494a5858fb1a462d5d687a6057349d013e20b93643545b` | Exit 0, no diagnostics; real 12.32 s, user 2.35 s, system 5.57 s |

Both modules have independent complete mathematical approval, including final
syntax corrections. The released hashes precede provenance notice insertion;
the committed source and imported report were subsequently frozen at the exact revision below.
The direct checks are not canonical builds or imported kernel reports.

## Exact-source canonical verification

Frozen source: `26dbf77709501643284144f4294c4d768966958b`. Completed parent: draft
[#8895](https://github.com/LionSR/TNLean/pull/8895), evidence `4aaa0256f74aa317cb0180856a9e2579c21b341e`.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical Geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Passed, exit 0 | 17.560 s | `48f9a1a8777e0e43fd1ea332f0146c3238e61ead13492a38d457f13796697d88` |
| Imported three-name report | `lake env lean docs/provenance/evidence/8758-fan-primary-contacts-axioms.lean` | Passed, exit 0 | 4.441 s | `491d89e1ada6c03fb20bdb749c9179d5381266199ab32d75dc5c77d8de4a0c6f` |

The complete raw logs retain exact command, revision, elapsed-time and exit-code
headers. Both commands completed without diagnostics. The imported report has
exactly three quoted declarations, all satisfying the unchanged standard
logical-foundation policy. Both modules, the Geometry aggregator, the report,
the two chapters and their parent retain all seven frozen byte sequences.

Strict promotion and the unchanged normal policy pass all 282 records. Exactly
three original rows are added. Every one of the 279 parent records and shards,
and all 124 tracked historical evidence files, remain unchanged; no old
declaration is reverified. Only the three newly promoted rows' historical
preparation descriptions clarify that verification had been pending before
source freeze. All dependency and toolchain bytes are unchanged.

Full source synchronization passes with `total_blueprint_refs = 20230` and
20,236 lines in `blueprint/lean_decls`, with complete reverse coverage and
no missing, stale or duplicate references. Imports cover
2,856 production modules in
75 files. The two scoped chapters contain
three theorems and three proofs, with six completion markers in total.
Independent review, pinned formatter idempotence, reader prose, module guards
and pattern checks pass. The separately recorded full direct checks remain
17.06 seconds for FanRunContacts and
12.32 seconds for PrimaryFineCellCover;
their user/system timings and released hashes are retained above.

Full CI and compiled book checking remain separate. The historical local
whole-library declaration check encountered missing
`TNLean/MPS/Examples/Fibonacci.olean`; its prior evidence and limitation are
retained. QICLean remains pinned to `8d5389d23c8e675a0117442e1a0d2c683a4bad41`.

Global primary/run interfaces, isolated stars, repairs and both headline
theorems remain open.
