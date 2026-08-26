# PEPS torus singleton blocking-datum deletion

This audit records the repository-local pass-through exception
(`docs/project_conventions.md` §Style) for the removal of
`TNLean/PEPS/SingletonEdgeBlockingData.lean` and
`TNLean/PEPS/TorusReferenceBlockingData.lean`.

## Why

The singleton datum builds a one-edge blocking datum out of two singleton vertex
blocks, which is injective only under **vertex injectivity** — a strictly
stronger hypothesis than the rectangular injectivity of Theorem 3 of
arXiv:1804.04964 (lines 1449--1452 of `Papers/1804.04964/paper_normal.tex`).
Under `CLAUDE.md` §Faithfulness rule it is therefore a specialization, not the
formalization of the source's reference datum. The source-faithful datum,
`TNLean/PEPS/TorusRectangleReferenceData.lean`, has been in place and is what
the translation-invariant gauge family consumes.

## Zero-consumer evidence

At the audited head neither file had a non-`Archive` consumer: the only imports
were from the generated aggregator `TNLean/PEPS.lean`; no `\lean{...}` tag under
`blueprint/src/` names any declaration below; the only prose references were the
`\leanid{}` footnote in `docs/paper-gaps/peps_normal_ft_section3_route.tex` (now
removed with the paragraph it annotated) and a docstring cross-reference in
`TNLean/PEPS/TorusRectangleReferenceData.lean` (now reworded). With the singleton
datum gone the accompanying **Scope restriction
(NormalTorusRectangleInjectivityHypotheses)** marker in that paper-gap note
described nothing in the library and was removed too.

## Removed declarations with replacements

All replacements live in `TNLean/PEPS/TorusRectangleReferenceData.lean`.

| Removed declaration | Replacement |
|---|---|
| `torusHorizontalReferenceBlockingDatum` | `torusHorizontalRectangleBlockingDatum` |
| `torusVerticalReferenceBlockingDatum` | `torusVerticalRectangleBlockingDatum` |
| `isCrossingEdge_torusHorizontalReferenceBlockingDatum` | `isCrossingEdge_torusHorizontalRectangleBlockingDatum` |
| `isCrossingEdge_torusVerticalReferenceBlockingDatum` | `isCrossingEdge_torusVerticalRectangleBlockingDatum` |
| `singletonEdgeBlockingData` | `torusHorizontalRectangleBlockingDatum` / `torusVerticalRectangleBlockingDatum` (the source-faithful rectangle construction; no singleton-block form is retained) |
| `singletonEdgeBlockingData_red` | as above — the red block is read off `torusHorizontalRectangleBlockingDatum` directly |
| `singletonEdgeBlockingData_blue` | as above — the blue block is read off `torusHorizontalRectangleBlockingDatum` directly |
| `singletonEdgeBlockingData_complement` | as above — the complementary block is read off `torusHorizontalRectangleBlockingDatum` directly |
| `isCrossingEdge_singletonEdgeBlockingData` | `isCrossingEdge_torusHorizontalRectangleBlockingDatum` / `isCrossingEdge_torusVerticalRectangleBlockingDatum` |
| `isCrossingEdge_singleton` | none needed — zero consumers; the crossing characterization used by the rectangle route is `isCrossingEdge_torusHorizontalRectangleBlockingDatum` |
| `isCrossingEdge_singleton_eq_ofAdj` | none needed — zero consumers; same as above |

## Correction to an earlier audit

`docs/audits/2026-08-04_issue_status_audit.md:30` states that
`torusHorizontalReferenceBlockingDatum` "feeds
`fundamentalTheorem_normalTorusPEPS_unconditional`
(`TorusFundamentalTheorem2.lean:298`)". That claim is **false**: the capstone's
hypotheses are `NormalTorusRectangleInjectivityHypotheses` and it consumes
`torusHorizontalRectangleBlockingDatum` (`TorusFundamentalTheorem2.lean:200--210`).
The singleton datum had no consumer at all.
