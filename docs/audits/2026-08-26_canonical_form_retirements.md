# Canonical-form retirement audit

Audited in the canonical-form layer: the phase-cover module
`TNLean/MPS/CanonicalForm/PhaseCover.lean`, the normal-commutant module
`TNLean/MPS/CanonicalForm/NormalCommutant.lean`, and the BNT-refinement
module `TNLean/MPS/CanonicalForm/BNTRefinement.lean`.

## Phase-cover forwards

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

## Dressed-adjoint specializations

`TNLean/MPS/CanonicalForm/NormalCommutant.lean` carried two theorems stated
only for a self-adjoint letter. That restriction is absent from the source,
which proves the relative two-gauge statement for an arbitrary letter, so the
restricted pair is a specialization rather than the source result. Both are
retired in favour of the unrestricted theorem, which carries the Blueprint
tag.

| Removed declaration | Single source of truth |
|---|---|
| `Kraus.IsNormal.conjTranspose_mul_self_eq_smul_one_of_dressed_adjoint` | `Kraus.IsNormal.gram_eq_pos_smul_gram_of_gram_conj_eq` (Blueprint `thm:eq3_of_dressed_adjoint`) |
| `Kraus.IsNormal.smul_mem_unitaryGroup_of_dressed_adjoint` | `Kraus.IsNormal.gram_eq_pos_smul_gram_of_gram_conj_eq` |

Neither removed name is cited by a Blueprint `\lean{...}` tag, and neither
had a consumer outside its own module.

## Grouped-position leftovers

The 2026-08-23 nonzero-coefficient cleanup
(`docs/audits/2026-08-23_nonzero_coefficient_convention.md`) replaced the
active/inactive coordinate apparatus. Three declarations survived that
cleanup without acquiring a consumer, and are retired here with no
replacement.

| Removed declaration | Replacement | Evidence |
|---|---|---|
| `MPSTensor.CPSVCanonicalFormData.groupedPosition` | none | zero references repo-wide |
| `MPSTensor.CPSVCanonicalFormData.groupedListedEquiv_groupedPosition` | none | zero references repo-wide |
| `MPSTensor.CPSVCanonicalFormData.BNTRefinement.groupedWeight_copy` | none | zero references repo-wide |

Because the 2026-08-23 note listed the last two as the replacements for
retired active-coordinate names, its mapping table is annotated in place: the
rows for `groupedListedEquiv_activeCopy` and
`ActiveBNTRefinement.groupedWeight_activeCopy` now record that their named
replacement was itself retired here, unused.

Every removal above burns down a slice of open ledger entry S2 (#4564).

## The duplicated copy-gauge carrier in the BNT refinement record (2026-08-27)

`MPSTensor.CPSVCanonicalFormData.BNTRefinement` carried the same gauge-phase
relation twice. The per-copy carrier `copyGauge` / `copyRelation` states, for
each displayed index $k$ and each letter $i$,
$$
  A_k^{\,i}=\zeta_k\,X_k\,C_{j(k)}^{\,i}\,X_k^{-1},
$$
where $C_{j(k)}$ is the chosen representative of the class of $k$ and $\zeta_k$
is the unit phase. The regrouped carrier states the same equation in two steps:
`regroupedBlocksEq` names the phase multiple $\zeta_k C_{j(k)}$ as the regrouped
block, and `blocksEqListedGaugeConj` conjugates it by `listedGauge`. In the sole
constructor of the record, `listedGauge` is assigned the very same gauge family
that `copyGauge` receives, and `regroupedBlocksEq` is `rfl`, so the two carriers
are populated from one witness. Every downstream projection reads the regrouped
carrier.

Separately, `ambientCoisometryEq` pinned the record's own `ambientCoisometry`
field to the parent record's `data.ambient_coisometry` by `rfl`, and nothing
read the pin. The coisometry property that downstream code does use is carried
by `ambientCoisometric`.

| Removed field | Surviving carrier |
|---|---|
| `MPSTensor.CPSVCanonicalFormData.BNTRefinement.copyGauge` | `listedGauge` |
| `MPSTensor.CPSVCanonicalFormData.BNTRefinement.copyRelation` | `regroupedBlocksEq` together with `blocksEqListedGaugeConj` |
| `MPSTensor.CPSVCanonicalFormData.BNTRefinement.ambientCoisometryEq` | `ambientCoisometric`, the property actually consumed |

None of the three names is cited by a Blueprint `\lean{...}` tag, and none had
a projection anywhere in `TNLean/` outside `Archive/`; the surviving occurrences
of the spellings `copyGauge` and `copyRelation` are the local names bound by the
`choose` in `exists_bntRefinement`, whose arity is fixed by the witness it
destructures. The structure docstring needed no edit: its clause about realizing
each copy as a gauged phase multiple of its representative remains true through
the regrouped carrier, and its ambient clause remains true through
`ambientCoisometric`. Net −21 Lean lines. This burns down a further slice of
open ledger entry S2 (#4564).
