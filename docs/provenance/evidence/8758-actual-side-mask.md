# Actual side subdivisions and contacts with the dummy neighborhood

Eight original declarations determine the midpoint subdivisions induced by
actual opposing fine-cell corners and exclude contact between the initial
dummy neighborhood and layers beyond the initial layer.

For a reference fine cell of layer $k$, let $[a_s,b_s]$ be its whole side
indexed by $s$. The actual subdivision mask divides this side exactly when
its midpoint is a corner of some actual fine cell in a layer $h\ge k_0$.
The quantifier includes nonbelt cells. The mask and its exact witness
characterization require no radius or late-layer assumption.

For every optional midpoint mask, an elementary segment is either the
whole side or one of its two midpoint halves. Its endpoints are therefore
the whole-side endpoints, the start and midpoint, or the midpoint and end;
the segment is contained in the whole side in every case. These two
geometric statements require no actual layer membership, radius bound or
late-layer assumption. Their previously private proofs are exposed for
reuse, with the mathematical argument unchanged.

If $C\ge2$, $k\ge50{,}000{,}000$, both fine-cell indices are actual layer
indices, and the opposing layer satisfies $h\ge k_0$, every opposing corner
on a resulting elementary segment is one of that segment's endpoints.
No additional lower bound on $h$, assumption $k\ge k_0$, distinct-cell
hypothesis or belt hypothesis is imposed. The whole-side corner trichotomy
first gives start, midpoint or end; a midpoint witness forces the mask to
be true, while each divided half retains only its two endpoints.

For a point $x$ in the closure of the initial dyadic neighborhood
$N_{k_0}$, there is an actual endpoint $p$ with

$$
\|x-p\|_\infty\le(C+1)2^{k_0}.
$$

Together with the closed-layer lower distance estimate, this gives, for
$x\in\overline{N_{k_0}}$, $y\in\overline{D_k}$ and $k\ge k_0+1$,

$$
(C-1)2^{k_0}\le\|x-y\|_\infty.
$$

The distance bound holds for every natural radius $C$; it is informative
when $C>1$. For $C\ge2$, a common closure point between $N_{k_0}$ and a
layer $D_k$ with $k\ge k_0$ therefore forces $k=k_0$. This index conclusion
requires no late-layer threshold or positive-length contact assumption.
No endpoint-set nonemptiness assumption is added: a point in the closed
neighborhood supplies an endpoint witness.

## Source, attribution and scope

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex`.

The actual side divisions are described in lines 299–310 in the proof of
`prop:two-families`. The initial dummy neighborhood and layers appear in
lines 160–177; the distance estimates use `geometry:layer-distance` in
lines 179–191. The opposing dummy region occurs in lines 299–306.
The corner theorem depends on the previously verified local mesh argument
at `geometry:initial-stars`, lines 352–356.

These statements establish an actual corner-induced subdivision and
localize dummy contacts to the initial layer. Classification of
positive-length contacts between two distinct fine cells, matching
opposing elementary segments, constancy of a primary or dummy identifier
along an open segment, consistent global labels, active rays, sectors and
the complete isolated-star and two-family constructions remain further
obligations.

Proofs are independently written; no upstream Lean source or proof text
is reused. OpenAI Codex (GPT-6) assists LionSR under #8758.
The work was publicly claimed under #8758 before execution:

- [actual midpoint subdivision](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046479723);
- [dummy-neighborhood contacts](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046553755);
- [contribution scope](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046663920);
- [reusable elementary-side geometry](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046753507).

## Exact source and canonical evidence

Frozen source revision: `f8b62e1b56c8f7e356c870322aa3418702349a68`.

The two production modules and the imported audit match the exact Git
bytes at that revision:

| Frozen file | SHA256 |
|---|---|
| `TNLean/PEPS/AreaLaw/Geometry/SideSubdivisionMask.lean` | `c564ff35ea9a33079237c38e207e7301e604ead888b502f545eceb4fb94e2d5e` |
| `TNLean/PEPS/AreaLaw/Geometry/DummyContacts.lean` | `d848dbf2aff6061a43991657197828b5f2adbc4feec0f49dba595c8dd87dc6ae` |
| `docs/provenance/evidence/8758-actual-side-mask-axioms.lean` | `f179641a0fc5895a8ca8a460242d276e8ec0c783306a55eb434ed68b753bed37` |

`TNLean/PEPS/AreaLaw/Geometry/SideSubdivisionMask.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.fineLayerSplitMask`;
- `TNLean.PEPS.AreaLaw.Geometry.fineLayerSplitMask_eq_true_iff`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFan_elementary_endpoints_cases`;
- `TNLean.PEPS.AreaLaw.Geometry.cellFan_elementary_segment_subset_whole`;
- `TNLean.PEPS.AreaLaw.Geometry.fineLayer_corner_on_elementarySide`.

`TNLean/PEPS/AreaLaw/Geometry/DummyContacts.lean`:

- `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_exists_dist_le`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_dist_later_layer`;
- `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood_contact_layer_eq`.

| Check | Actual command | Exit code | Elapsed seconds |
|---|---|---|---|
| Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | 0 | 59.834 |
| Imported eight-name audit | `lake env lean docs/provenance/evidence/8758-actual-side-mask-axioms.lean` | 0 | 30.477 |

Both canonical commands passed at the exact frozen source in the existing
warmed worktree under the shared repository lock, reusing the pinned prebuilt
Mathlib artifacts. The build compiled only `DummyContacts`, `SideSubdivisionMask`
and their `Geometry` aggregator, with no warnings or errors. The eight imported
reports each list only `propext`, `Classical.choice` and `Quot.sound`.
The source-only preparation worktree has no `.lake` directory and performs
no cache or build operation. The mask source
passed non-mutating package-option elaboration in 5.5077 seconds without
diagnostics before the two private geometric lemmas were exposed for reuse.
Independent mathematical review retains the review of those unchanged proofs.
After the two geometric lemmas became public, the source passed a further
direct package-option check without
diagnostics; no elapsed time was recorded for that check. The completed dummy
source also passed direct package-option elaboration and independent
mathematical review. The two blueprint chapters state the exact quantifiers
and conclusions and were reviewed independently.

Evidence paths and SHA256 hashes:

- `docs/provenance/evidence/8758-actual-side-mask-build.log`: `3e6af220dca21f07173481916a3f1f82519dd3d72b8acf8c0a66abf3e17ebcca`;
- `docs/provenance/evidence/8758-actual-side-mask-axioms.log`: `477586bce5162191ccde32d8408fb9518e83d6888dd072b7d94496f80039e3af`.

Each log records its exact command, frozen revision, elapsed time and exit
code. Trailing whitespace alone was normalized; the actual build output and
all eight axiom reports are retained.

## Provenance and integration

The parent is `41a653ac31622d5348cc9fcf94b98c49df090fac` with 251 inventory
entries. All parent shard bytes, proof sources and evidence are preserved,
including the original and reverified fan/primary records and the earlier
first-check warning logs. The previously existing planned root-ledger
entry remains planned.

The strict helper promoted precisely the eight new rows after these actual
checks. The complete 259-entry current-policy audit passed, including the
exact eight source declarations, original-proof notices, imported audit
names, licenses and pinned manuscript labels. It validates the immutable
251-row byte baseline against the parent Git objects. No parent verification
is replaced.

The complete blueprint source synchronization passed with 20,213 distinct
references and 20,207 flattened records; its report has `sync_ok: true` and
no missing, stale or duplicate entries. Complete changed-declaration coverage
also passed relative to the 251-row parent. The two chapters contain six
mathematical environments, eight declaration records and five proof tags.
Generated imports are current at 75 imports and 2,845 modules. The mathematical
prose and exact hypotheses were independently reviewed. Formatter idempotence
passed for both chapters, including the grouped elementary-side theorem:
formatted temporary copies equal the current and exact frozen Git bytes.
The final reader-facing prose check passed at the same frozen revision.
Independent review approved all eight statements and their mathematical proofs,
including the unchanged geometric arguments previously reviewed as private lemmas.
The grouped elementary-side blueprint theorem was independently reviewed at
the frozen revision: it records all three oriented endpoint cases and whole-side
containment for an arbitrary optional midpoint subdivision.

The historical local whole-library `leanblueprint checkdecls` failure
caused by a missing pre-existing `Fibonacci.olean` artifact remains
preserved; that unrelated check is not repeated here. Full-library CI,
compiled blueprint declaration checking and rendering remain pending.
