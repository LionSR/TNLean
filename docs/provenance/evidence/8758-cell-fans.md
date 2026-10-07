# Fans within a square cell: verification pending

Twelve proposed declarations describe the fan obtained from the center
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

The proposed covering equality is

$$
\bigcup_i P_i=\overline{\operatorname{dyadicCell}(o,\ell,z)}.
$$

For every pair $i,j$, including $i=j$, the proposed intersection equality
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

The exact statements are recorded from the authors. The first eight fan
proofs passed direct elaboration with the package options, without warnings,
and independent mathematical review. The marked-vertex connection and the
combined final source inventory are pending; canonical verification remains
pending.

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

These are exact proposed statements. Their proofs and the final combined
source inventory remain under development.

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

## Proposed exact inventory

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

The combined shard is `docs/provenance/openai-math.d/8758-cell-fans.json`.
All twelve entries remain planned, with proposed names and pending
verification. CellFanSlot is an abbreviation using existing Sigma and Fin
types, followed by four fan definitions and four fan theorems. The nonbelt
module adds one definition and two theorems. No new public constructor is
proposed; the final elaborated inventory remains pending.

The immutable prior inventory contains 225 entries at
`c9debcc6060616b0eb1af6f8f02dcacdacc73e8a`, after the completed initial-family
evidence was published in [TNLean #8862](https://github.com/LionSR/TNLean/pull/8862)
and merged into preparation. All prior entries and their evidence remain
unchanged. This inventory includes the previously existing planned
root-ledger entry; it is not a claim that all 225 entries have been compiled.
The four initial-family parent entries retain their actual verified source
and logs.

## Canonical evidence to be recorded

Exact frozen source revision: **Pending**.
Published pull request and evidence head: **Pending**.

| Check | Expected command | Result | Elapsed seconds |
|---|---|---|---|
| Changed Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | Pending | Pending |
| Imported twelve-name audit | `lake env lean docs/provenance/evidence/8758-cell-fans-axioms.lean` | Pending | Pending |

Canonical commands must run from the existing warmed TNLean worktree through
`scripts/lake_build_locked.sh`, under the shared repository lock and with the
pinned prebuilt Mathlib artifacts. The source-only preparation worktree
performs no cache or build operation. Optional direct elaboration uses the
warmed environment and is recorded separately from the canonical target.

The final record must identify actual commands, frozen source, elapsed times,
exit codes, module diagnostics and SHA256 hashes of
`8758-cell-fans-build.log` and `8758-cell-fans-axioms.log`. Any normalization
of captured whitespace must be described. The exact audit prints each
selected imported public name; its actual dependencies are recorded after
the audit completes.

Exact proposed signatures and declaration kinds: **Recorded from the author**.
Final elaborated source, notices and imported-name inventory: **Pending**.
Complete 237-entry provenance/schema/pinned-source/license validation:
**Pending**.
Independent mathematical review: **Pending**.
Blueprint source synchronization and reverse coverage: **Pending**.
Formatter and generated-import checks: **Pending**.
Full-library CI, compiled blueprint declaration checking and rendering:
**Pending**.

Promotion changes only these twelve new entries after the exact
committed-source build and imported-name audit pass. Every prior 225 entry
remains byte-identical to the captured completed-parent baseline. The
static promotion helper writes its reviewed output in `/tmp` and does not
run Lean or modify a build cache.

The earlier primary-region work recorded a whole-library local
`leanblueprint checkdecls` failure caused by a missing pre-existing
`Fibonacci.olean` artifact. That historical failure log remains intact.
Compiled blueprint checking and rendering are tracked separately in CI.
