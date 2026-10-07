# Uniqueness of the region opposing an elementary side

The two new proofs are complete and independently reviewed. Their provenance
records remain planned until a frozen source revision has actual canonical
build and imported kernel reports. The completed parent is
`eda992e719dd7161906b54b20a057992037b44cb` (PR #8888). No new canonical
verification is recorded.

## Mathematical scope

The common elementary-side geometry theorem is promoted from an existing
private proof. For every origin, natural dyadic exponent, signed integer
cell index, optional midpoint subdivision and elementary slot, its two
endpoints are distinct. Either their first coordinates agree with a first
boundary coordinate of the square or their second coordinates agree with
a second boundary coordinate. No layer-membership or late-scale assumption
is imposed.

The uniqueness theorem has exactly the assumptions of opponent
existence: common origin and finite endpoint set, C ≥ 2, reference layer
k ≥ 50000000, k₀ ≤ k, actual fine-layer membership and any slot of its
exact actual midpoint subdivision. It asserts a unique tag in
`Option (ℕ × (ℤ × ℤ))`. The `none` tag means that the entire elementary
segment lies in the closure of the initial dummy neighborhood. A tag
`some (h,w)` requires h ≥ k₀, actual opposing fine-cell membership,
distinctness from the reference indexed cell and containment of the
entire segment in that cell's closure. The dummy neighborhood is one
region even when it has several contributing coarse cells.

No uniqueness, contact, plane-cover, nonempty-Z, label or sparsity premise
is supplied. The released proof passed the reported package-option direct check without
diagnostics in 12.76 seconds (user 8.28 seconds, system 9.92 seconds).
Independent mathematical review approved its exact hypotheses, whole-segment
conclusion, empty cases and treatment of the dummy neighborhood as one region.
The common geometry statement and proof equal the completed parent private
lemma after its name and visibility change; the old existence statement is
unchanged and its proof differs only in the two renamed helper calls. Region labels, ray and sector constructions, subsequent
repairs, descendants, isolated stars, the global two-family partition
and both headline area-law theorems remain further obligations.

## Manuscript and independence

- Manuscript: OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11.
- Immutable source revision:
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- Manuscript path:
  `preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.
- Source label: `prop:two-families`; lines 299–310 for elementary geometry
  and lines 299–316 for the opposing region.
- The records describe original formalizations from mathematical manuscript
  statements; no upstream Lean proof text is reused. The common geometry
  proof is reused within TNLean by promoting its existing private theorem.
  OpenAI Codex (GPT-6) assistance is disclosed.

## New declaration inventory

All names are in `TNLean.PEPS.AreaLaw.Geometry`.

| Module | New theorem | State |
| --- | --- | --- |
| `ElementarySideOpponents.lean` | `cellFan_elementary_geometry` | Proof complete and reviewed; canonical verification pending |
| `ElementarySideOpponentUniqueness.lean` | `exists_unique_elementarySide_opponent` | Proof complete and reviewed; canonical verification pending |

The older opponent file also exports `exists_elementarySide_opponent`.
That existing theorem is included in the same imported report and receives
fresh verification because its complete source file changes. Its public
statement, identity, source mapping, license and original notice remain
unchanged.

## Verification

Completed parent revision: `eda992e719dd7161906b54b20a057992037b44cb`.
Frozen source revision: **unbound**.

| Check | Command | Outcome | Time | Log SHA-256 |
| --- | --- | --- | --- | --- |
| Canonical geometry build | `lake build TNLean.PEPS.AreaLaw.Geometry` | Pending | Pending | Pending |
| Imported three-name report | `lake env lean docs/provenance/evidence/8758-unique-side-opponents-axioms.lean` | Pending | Pending | Pending |

Released-source direct elaboration and independent mathematical review have
passed. Canonical checks, complete source synchronization and reverse coverage,
generated imports, full CI and rendering remain pending. Pinned chapter formatting is complete and idempotent. The scoped chapter
contains two theorem environments, two declaration records and two proofs;
all references to prior statements resolve. Static validation against the
unchanged current policy passed all 272 entries, projecting only the changed
old existence record to pending in memory. All 270 production parent ledger
entries remain byte-identical at this preparation stage. The other 269
entries and all 112 historical evidence files are immutable through promotion. The historical local
whole-library blueprint limitation due to the missing pre-existing
`TNLean/MPS/Examples/Fibonacci.olean` must remain recorded.

## Parent evidence retention

The completed parent collection contains 270 entries at
`eda992e719dd7161906b54b20a057992037b44cb`. The baseline was captured from
that clean warmed worktree, independently of the modified source-preparation
worktree. It preserves all 112 tracked files recursively under
`docs/provenance/evidence`, including every historical note, imported report,
log and the nested orthogonalization evidence. A narrower initial capture
was preserved unchanged as a superseded temporary artifact; the strict
helper uses the separately named complete-history baseline and requires
its file inventory to equal the parent's recursive Git inventory.

This contribution adds two entries, for 272 in total. It reverifies only
`exists_elementarySide_opponent` in `8758-actual-side-matching.json` and
preserves all 269 other parent entries and every unaffected shard. An
explanation of the unchanged private-proof promotion is appended to the
existing entry, and only its verification record is replaced after actual
canonical success. The original exact-source revision is
`93c807b97f45312bab807ba47abb06f11d686f18`. Its ledger, imported report,
evidence note and historical logs remain preserved at the completed parent.

| Reverified declaration | Original source | Original evidence | Reason |
| --- | --- | --- | --- |
| `exists_elementarySide_opponent` | `93c807b97f45312bab807ba47abb06f11d686f18` | `8758-actual-side-matching.md` and its build/imported logs | The unchanged private elementary-geometry proof becomes public in the same file; two callers use its new name. |

Original build-log SHA-256:
`2b7fd47586ea1bf7da6c571cf3be91e3bce16020f84e0d56ff73fdab564e763b`.
Original imported-report-log SHA-256:
`aff033950f86160e42250ecfd19672fdc60a2f87552127cf3d10a612cca946cf`.

The mixed-file validation must recognize both public names and both
original notices in `ElementarySideOpponents.lean`; only the promoted
geometry theorem is a new row. No parent record is replaced by this
prospective preparation.
