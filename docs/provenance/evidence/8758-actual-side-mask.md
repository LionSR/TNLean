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
Public claims: [actual side mask](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046479723),
[dummy contacts](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046553755),
and [shared side geometry](https://github.com/LionSR/TNLean/issues/8758#issuecomment-6046753507).

## Exact source and canonical evidence

Frozen source revision: **Pending**.

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
| Geometry target | `lake build TNLean.PEPS.AreaLaw.Geometry` | Pending | Pending |
| Imported eight-name audit | `lake env lean docs/provenance/evidence/8758-actual-side-mask-axioms.lean` | Pending | Pending |

Canonical verification must use the exact frozen source in the existing
warmed worktree under the shared repository lock and the pinned prebuilt
Mathlib artifacts. The source-only preparation worktree has no `.lake`
directory and performs no cache or build operation. The mask source
passed non-mutating package-option elaboration in 5.5077 seconds without
diagnostics before the two private geometric lemmas were exposed for reuse.
Independent mathematical review retains the review of those unchanged proofs.
The completed dummy
source also passed direct package-option elaboration and independent
mathematical review. The two blueprint chapters state the exact
quantifiers and conclusions; canonical verification remains pending.

Evidence paths and SHA256 hashes:

- `docs/provenance/evidence/8758-actual-side-mask-build.log`: **Pending**;
- `docs/provenance/evidence/8758-actual-side-mask-axioms.log`: **Pending**.

Each completed log must record its exact command, frozen revision,
elapsed time and exit code. Only trailing whitespace may be normalized;
actual diagnostics and quoted axiom reports must be retained.

## Provenance and integration

The parent is `41a653ac31622d5348cc9fcf94b98c49df090fac` with 251 inventory
entries. All parent shard bytes, proof sources and evidence are preserved,
including the original and reverified fan/primary records and the earlier
first-check warning logs. The previously existing planned root-ledger
entry remains planned.

The eight new rows remain planned until actual canonical verification.
The static helper checks the exact eight source declarations, original-proof
notices, imported audit names, licenses, pinned manuscript labels and the
259-entry schema. It validates the immutable 251-row byte baseline
against the parent Git objects. No parent verification is replaced.

Strict promotion: **Pending**.
Complete blueprint source synchronization and reverse coverage: **Pending**.
Formatter, prose and generated imports: **Pending**.
Independent review approved all eight statements and their mathematical proofs,
including the unchanged geometric arguments previously reviewed as private lemmas.

The historical local whole-library `leanblueprint checkdecls` failure
caused by a missing pre-existing `Fibonacci.olean` artifact remains
preserved; that unrelated check is not repeated here. Full-library CI,
compiled blueprint declaration checking and rendering remain pending.
Published pull request and evidence head: **Pending**.
