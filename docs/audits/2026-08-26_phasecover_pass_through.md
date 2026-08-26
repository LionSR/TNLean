# Phase-cover pass-through audit

Audited in the canonical-form phase-cover module
`TNLean/MPS/CanonicalForm/PhaseCover.lean`.

The project pass-through exception (`docs/project_conventions.md` §Style)
applies to the family-indexed phase-equivalence lemmas: each is a literal
forward to the block-level lemma of the same name, every non-Archive consumer
is migrated to the block-level owner, and no Blueprint tag names any of them.

| Removed declaration | Single source of truth | Migrated consumer |
|---|---|---|
| `MPSTensor.MPVPhaseEquiv.refl` | `MPSTensor.MPVBlockPhaseEquiv.refl` | `mpvPhaseSetoid` |
| `MPSTensor.MPVPhaseEquiv.symm` | `MPSTensor.MPVBlockPhaseEquiv.symm` | `mpvPhaseSetoid` |
| `MPSTensor.MPVPhaseEquiv.trans` | `MPSTensor.MPVBlockPhaseEquiv.trans` | `mpvPhaseSetoid` |
| `MPSTensor.MPVPhaseEquiv.of_gaugePhaseEquiv_cast` | `MPSTensor.MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast` | `mpvPhaseClassData` |
| `MPSTensor.MPVPhaseEquiv.exists_mpvState_eq_smul` | `MPSTensor.MPVBlockPhaseEquiv.exists_mpvState_eq_smul` | none remaining |

Two further declarations are retired outright, with no replacement, because
they have no consumer anywhere outside their own definition:

| Removed declaration | Replacement | Evidence |
|---|---|---|
| `MPSTensor.MPVPhaseClassData.representative_mpv_span_eq` | none | zero references repo-wide; one of the zero-reference declarations recorded by ledger entry S2 (#4564) |
| `MPSTensor.MPVBlockPhaseEquiv.exists_mpvState_eq_smul` | none | its only caller was the family-indexed forward retired above, whose only caller was `representative_mpv_span_eq` |

The definition `MPSTensor.MPVPhaseEquiv` itself is retained: it is
Blueprint-tagged at `blueprint/src/chapter/ch10_bnt_sector_canonical_form.tex`
under `def:mpv_phase_class_data`, and it remains both the relation of
`mpvPhaseSetoid` and the type of the `enum_phase` field of
`MPVPhaseClassData`. Only its forwarding lemma family is retired; callers now
name the block-level lemmas directly.

`docs/audits/2026-04-26_issue877_after_blocking_sector.md` mentions
`representative_mpv_span_eq` and is intentionally left unchanged: it is a dated
historical snapshot.
