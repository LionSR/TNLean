# Blueprint declaration ownership for shared results

This note records the ownership convention used to resolve the declaration clusters
identified in issue #6244.  It precedes the corresponding changes to the blueprint.

## Convention

Each Lean declaration has exactly one blueprint entry carrying its `\lean{...}` tag.
That entry is the one in which the result has its most general mathematical role.  A
later specialization, application, or recap cites the owning entry through `\uses`:

- a statement cites the owner only when the owned result is needed to formulate the
  statement;
- a proof cites the owner only when the argument uses the owned result.

Displayed order alone does not determine ownership.  In particular, a contextual
application does not acquire ownership merely because it occurs before the general
discussion in the compiled book.

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
except for the Choi-rank remark, whose statement depends on the Chapter 4 definition and
minimality theorem.

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

The Chapter 21 definition cites the Chapter 23 definition at statement level.  Its two
structural theorems and the unitary-implementation theorem cite the corresponding
Chapter 23 results in their proofs.

## Cyclic trace expansion: Chapters 13 and 24

Chapter 13 owns `MPSTensor.trace_evalWord_eq_sum_cyclic`: it states the general cyclic
trace expansion for a closed MPS chain.  Chapter 24 uses this identity to identify the
coefficients of a cycle PEPS tensor, so the proof of that identification cites the
Chapter 13 theorem.

All eighteen shared declarations therefore have an unambiguous general owner.  No case
in these three clusters needs to retain two ownership tags.
