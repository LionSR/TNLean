# Blueprint declaration ownership for shared results

This note records the ownership convention used to resolve the declaration clusters
identified in issue #6244.  It precedes the corresponding changes to the blueprint.

## Convention

Each Lean declaration has exactly one blueprint entry carrying its `\lean{...}` tag.
That entry is the one in which the result has its most general mathematical role.  A
later specialization, application, or recap in the same compiled volume cites the
owning entry through `\uses`:

- a statement cites the owner only when the owned result is needed to formulate the
  statement;
- a proof cites the owner only when the argument uses the owned result.

Displayed order alone does not determine ownership.  In particular, a contextual
application does not acquire ownership merely because it occurs before the general
discussion in the compiled book.

When this note was written, Chapters 23 and 24 were excluded from
`blueprint/src/content.tex`, so a dependency edge between one of those chapters and
the compiled Chapters 13 or 21 was unresolved by `leanblueprint`.  In such a
cross-scope case the contextual entry relinquished its duplicate `\lean{...}` tag
without acquiring an invalid `\uses` edge, and the edge was deferred until both
entries belonged to a common compiled volume.

That exemption no longer applies.  `blueprint/src/content.tex` now inputs both
chapters, every entry named below is reachable from it, and the deferred edges were
added on 2026-09-19; see
`docs/audits/2026-09-19_blueprint_duplicate_declaration_tags.md`.  A breach of the
convention is now reportable: `python3 scripts/blueprint_lean_sync.py --ci
--report-duplicate-tags` fails when one declaration carries a `\lean{...}` tag in
two entries.

## Channel representations: Chapters 4 and 16

Chapter 4 owns the shared declarations.  It develops rectangular Kraus maps and the
corresponding Choi theory, while Chapter 16 explicitly presents itself as a continuation
and recap of this earlier channel theory.  The twelve shared declarations are:

- `Channel.HasKrausCard`;
- `Channel.HasKrausRankLE`;
- `Channel.choiRank`;
- `Channel.choiRank_le_of_hasKrausCard`;
- `Channel.hasKrausCard_choiRank_of_cp`;
- `kraus_conjTranspose_mul_eq_of_map_eq`;
- `kraus_dual_eq_of_map_eq`;
- `kraus_isometry_freedom_iff`;
- `kraus_same_map_of_isometry_combination`;
- `kraus_sum_conjTranspose_mul_of_tp`;
- `kraus_unitary_freedom_iff`;
- `spectralRadius_le_one_of_forall_eigenvalue_norm_le_one`.

The Chapter 16 entries cite the appropriate Chapter 4 owner through proof dependencies,
except for the Choi-rank remark: its statement depends on the Chapter 4 rank definition,
whereas its proof depends on the minimality theorem.

## Per-block linear extensions: Chapters 21 and 23

Chapter 23 owns the shared declarations because it develops the per-block linear
extension as part of the general algebraic Fundamental Theorem.  Chapter 21 uses the
same construction in the more specific MPDO/RFP discussion.  The five shared
declarations are:

- `MPSTensor.perBlockLinearExtension`;
- `MPSTensor.perBlockLinearExtension_spec`;
- `MPSTensor.perBlockLinearExtension_mul`;
- `MPSTensor.perBlockLinearExtension_bijective`;
- `MPSTensor.exists_unitary_conj_of_positive_perBlockLinearExtension`.

The Chapter 21 entries relinquished their duplicate ownership tags.  The two chapters
now occur in a common compiled volume, so the deferred edges were added: the Chapter
21 definition cites the Chapter 23 definition at statement level, and its
multiplicativity, bijectivity, and unitary-implementation results cite the
corresponding Chapter 23 results at proof level.

## Cyclic trace expansion: Chapters 13 and 24

Chapter 13 owns `MPSTensor.trace_evalWord_eq_sum_cyclic`: it states the general cyclic
trace expansion for a closed MPS chain.  Chapter 24 uses this identity to identify the
coefficients of a cycle PEPS tensor, so the proof of that identification cites the
Chapter 13 theorem mathematically.  The Chapter 24 entry relinquished its duplicate
ownership tag, and the proof-level `\uses` edge to the Chapter 13 theorem was added
once the two chapters occurred in a common compiled volume.

All eighteen shared declarations therefore have an unambiguous general owner.  No case
in these three clusters needs to retain two ownership tags.
