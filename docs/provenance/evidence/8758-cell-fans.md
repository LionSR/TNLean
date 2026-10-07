# Cell fans and the primary regions of nonbelt cells

Twelve original declarations describe the fan obtained from the center
of a square cell and its elementary boundary segments. Each side is either
left intact or divided at its midpoint. Joining the center to the segment
endpoints gives between four and eight closed triangles.

For arbitrary midpoint choices on the four sides, the position type is

$$
\coprod_{d=0}^{3}\{0,\ldots,n_d-1\},\qquad
n_d=\begin{cases}2&\text{if side }d\text{ is divided},\\
1&\text{otherwise}.\end{cases}
$$

It uses the existing finite types and introduces no new constructor.
Its cardinality lies between four and eight. For origin $o$, natural
side exponent $\ell$ and integer cell index $z$, let $c$ be the actual
cell center and let $a_i,b_i$ be the endpoints of the elementary segment
indexed by $i$. The fan polygon $P_i$ is the actual triangle with vertices
$c,a_i,b_i$.

The covering equality is

$$
\bigcup_i P_i=\overline{\operatorname{dyadicCell}(o,\ell,z)}.
$$

For every pair $i,j$, including $i=j$, the intersection equality
is

$$
P_i\cap P_j=\{c\}\cup
\bigcup_{u\in[a_i,b_i]\cap[a_j,b_j]}[c,u].
$$

In particular, the common center remains in the intersection when the
perimeter segments have empty intersection. The right-hand side is the
center together with its convex join to the intersecting perimeter segments.
The additional marked-vertex theorem places the actual center in the
existing nine-point cell-mark set and, for every elementary position, places
both of its perimeter endpoints in that same set. It holds for arbitrary
origin, natural scale, integer cell index and midpoint choices.

All twelve declarations and the eight mathematical blueprint entries
passed independent review. The actual vertices, covering, intersection and
nonbelt-primary statements are verified at the source revision below.

## The primary containing a nonbelt cell

The three additional declarations in `NonbeltPrimaries.lean` identify the
actual primary birth region of a nonbelt fine cell. Let $\ell\le k$ and
$\ell\le p$, put $q=2^{p-\ell}$, and choose the two belt residues
$a,b\in\{0,\ldots,q-1\}$. The origin, finite endpoint set and natural
layer parameter are arbitrary. If $z$ belongs to the actual fine-layer
index set at scale $\ell$ and lies outside the selected belt-cell indices,
define its pitch index by

$$
j(z)=\left(\left\lfloor\frac{z_1-a}{q}\right\rfloor,
\left\lfloor\frac{z_2-b}{q}\right\rfloor\right).
$$

The definition uses Euclidean integer division, which agrees with these
floors because $q>0$. The closure of the actual fine cell indexed by $z$
lies in the primary birth region with pitch index $j(z)$. Moreover, there
is a unique occupied pitch index whose actual primary birth region contains
that closed cell. The occupied pitch index is required to belong to the
finite set of actual primary pitch indices. No hypothesis $k\le p$ or
endpoint-set nonemptiness is imposed.

These conclusions hold for the actual fine cells and primary birth regions.
Their definitions and proofs passed the combined canonical verification.

## Source, attribution and scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The midpoint divisions of fine-cell sides are described in lines 299–306.
The fan from the center to the elementary segment endpoints is described
in lines 308–310, within the proof of `prop:two-families`. The actual
nine-point cell-mark connection additionally uses lines 325–330, immediately
before `geometry:initial-stars`. The nonbelt
primary identification is anchored in lines 212–218, `geometry:primary-pieces`
in lines 237–249, and the opposing-region statement in lines 299–305.

The present contribution is the geometry of these individual cell fans
and the actual primary containing each nonbelt fine cell.
Identification of the divisions induced by actual opposing cells,
consistent label assignment across shared sides, merging equal-label runs,
active rays and sectors, the full isolated-star statement, recursive
replacements and the complete two-family construction remain separate
obligations. The fan polygons alone do not establish either manuscript
headline theorem.

Proofs are independently written; no upstream Lean source or proof text
is reused. OpenAI Codex (GPT-6) assists LionSR under the existing
[TNLean #8758 fan claim](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045048500)
and its [nonbelt-primary extension](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045170965),
with the [marked-vertex connection](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6045372605).

## Exact source and canonical evidence

Exact verified source: `8d3f5cd9d9bb6c327eae8b90452ce3caecd406c2`.
The twelve audited declarations are:

`TNLean/PEPS/AreaLaw/Geometry/CellFans.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.CellFanSlot`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanCenter`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanStart`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanEnd`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanPolygon`;
- `TNLean.PEPS.AreaLaw.Geometry.card_cellFanSlot_bounds`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanPolygons_cover`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFanPolygons_inter_eq`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFan_vertices_mem_beltCellMarks`.

`TNLean/PEPS/AreaLaw/Geometry/NonbeltPrimaries.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.nonbeltPitchIndex`;
- `TNLean.PEPS.AreaLaw.Geometry.closure_nonbeltCell_subset_primaryBirthRegion`;
- `TNLean.PEPS.AreaLaw.Geometry.exists_unique_primary_of_nonbeltCell`.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Combined Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | 0 | 17.803 |
| Imported twelve-name audit | `lake env lean docs/provenance/evidence/8758-cell-fans-axioms.lean` | 0 | 6.257 |

`NonbeltPrimaries` compiled in 10 seconds, `CellFans` in 11 seconds and the
Geometry aggregator in 2.4 seconds, without warnings. The actual imported
axiom reports are:

- `CellFanSlot`: no axioms;
- `nonbeltPitchIndex`: `propext` only;
- the other ten declarations: `propext`, `Classical.choice` and `Quot.sound`.

The canonical commands ran from the existing warmed TNLean worktree under
the shared repository lock, through `scripts/lake_build_locked.sh --`,
reusing the pinned prebuilt Mathlib artifacts. The source-only preparation
worktree had no `.lake` directory and performed no cache or build operation.
The source also passed non-mutating elaboration with the package options
from the warmed environment.

Evidence log paths and SHA256 hashes:

- `8758-cell-fans-build.log`: `3f4dc3db379953712828ec6f6e90832c954f49c91466d5a51f137e2a0ef34e18`;
- `8758-cell-fans-axioms.log`: `38e7af9f3f7d983eef54b669b5e3b04d7c6ed96cb3ebeedd2937213a636fa260`.

Each actual log records its command, frozen source revision, elapsed time
and exit code. Only trailing whitespace was normalized; build diagnostics
and the quoted axiom reports are preserved.

## Provenance and integration

Strict static promotion passed for precisely the twelve new entries in
`docs/provenance/openai-math.d/8758-cell-fans.json`. The complete 237-entry
current-policy provenance/source/license/notice audit passes, including
exact module and committed audit bytes at the verified source, command
headers, actual evidence hashes and all twelve imported names.

The prior 225 inventory entries remain byte-identical to the completed
parent at `c9debcc6060616b0eb1af6f8f02dcacdacc73e8a`, including the previously
existing planned root-ledger entry. Their proof sources and evidence remain
unchanged. The completed initial-family parent entries retain their actual
verified source and logs.

Complete blueprint source synchronization passed with 20,191 distinct
public references and 20,185 flattened theorem-like declaration records.
The twelve new declarations belong to eight mathematical environments;
the report counts twelve formalized declaration records and six checked
proof tags for this contribution. The full JSON report has `sync_ok: true`
and no missing, stale or duplicate references. Reverse coverage reports
no changed declarations missing blueprint entries.

Formatter idempotence, reader-facing prose and generated imports passed;
75 generated files cover 2,840 production modules. Independent review
approved all twelve declarations and eight blueprint entries. Scoped proof
review found no new repeated pattern; the full scan reported pre-existing
patterns already recorded or rejected in the tactic ledger.

The earlier primary-region work recorded a local whole-library
`leanblueprint checkdecls` failure caused by a missing pre-existing
`Fibonacci.olean` artifact. That historical failure log remains intact; the
unrelated check was not repeated locally for this contribution. Full-library
CI, compiled blueprint declaration checking and rendering remain pending.
Publication branch: `feat/area-law-cell-fans`, stacked on the initial-mark-family contribution #8862. The source and exact evidence are committed together with the completed provenance records; the pull request is created after this evidence commit. No main-branch merge is performed.
