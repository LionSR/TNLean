# PEPS torus translate-blocking module deletion

This audit records the repository-local pass-through exception
(`docs/project_conventions.md` §Style) for the removal of
`TNLean/PEPS/TorusBlockingData.lean` and all six of its declarations.

## Why

The module specialized the general blocking-datum transport
(`transportBlockingDataAlong`, `TNLean/PEPS/RegionTransportData.lean`) along a
torus translation, so that a single reference blocking datum at an orientation
class's reference edge could be carried to every translate of that edge. It was
stranded by PR #7211, which removed `TNLean/PEPS/TorusReferenceBlockingData.lean`
— the reference-datum construction whose docstring was this module's last
in-tree mention.

The live torus route never took the translation path. It obtains per-edge data by
instantiating `torusHorizontalRectangleBlockingDatum` and
`torusVerticalRectangleBlockingDatum` at each rectangle offset
(`TNLean/PEPS/TorusRectangleGauge.lean`,
`TNLean/PEPS/TorusCovariantAbsorbedFamily.lean`) rather than by translating one
reference datum, which is why the translation route acquired no consumer.

## Zero-consumer evidence

At the audited head none of the six declarations had a non-`Archive` Lean
consumer. The module's only importers were the generated aggregator
`TNLean/PEPS.lean` and two files that needed nothing from it:
`TNLean/PEPS/TorusEdgeGauge.lean` (uses no translation identifier at all; its
import is now `TNLean.PEPS.TorusLatticeGraph`) and
`TNLean/PEPS/RegionTransferCovariance.lean` (needs only `translate` and
`IsTorusTranslationInvariant`; its import is now
`TNLean.PEPS.TorusTranslationInvariant`). No `\lean{...}` tag under
`blueprint/src/` names any of the six. The only prose references were two
`\leanid{}` entries in `docs/paper-gaps/peps_normal_ft_section3_route.tex`,
removed here together with the sentence they annotated — following the precedent
of `docs/audits/2026-08-26_peps_torus_singleton_blocking_deletion.md`, which
removed a footnote together with its paragraph rather than leaving prose
asserting a formalization that no longer exists. The general-transport sentence
and its four surviving `\leanid{}` entries are untouched.

## Removed declarations with replacements

| Removed declaration | Replacement |
|---|---|
| `regionInjectivityDataOf_translate_eq` | the translation-invariance fixed-point equation `hA a b` used directly at the site |
| `translateBlockingData` | `transportBlockingDataAlong A (translate a b) D` |
| `translateBlockingData_red` | the corresponding projection of `transportBlockingDataAlong` (definitional, `rfl`) |
| `translateBlockingData_blue` | the corresponding projection of `transportBlockingDataAlong` (definitional, `rfl`) |
| `translateBlockingData_complement` | the corresponding projection of `transportBlockingDataAlong` (definitional, `rfl`) |
| `isCrossingEdge_translateBlockingData` | `isCrossingEdge_transportBlockingDataAlong` at `translate a b` |

## Follow-on, not folded in here

With this module gone, `transportBlockingDataAlong` and
`isCrossingEdge_transportBlockingDataAlong` in
`TNLean/PEPS/RegionTransportData.lean` lose their only consumer; whether
`TNLean/PEPS/SquareLatticeCoordinateSwap.lean`, the one remaining non-aggregator
importer, uses anything from that module is worth a separate check.

Separately, the same footnote block in the paper-gap note cites five names absent
from the tree — `torusOrientationUniformGauge`,
`IsTorusOrientationUniformGaugeFamilyModScalar`,
`isTorusOrientationUniformGaugeFamilyModScalar_of_classAgreement`,
`isTorusOrientationUniformGaugeFamilyModScalar_of_translationInvariant`, and the
siblings of `exists_regionEdgeGauge_torus` in that list. That is pre-existing
documentation drift, unrelated to this deletion, and wants its own cleanup.
