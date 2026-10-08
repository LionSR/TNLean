# Exact-counting review repair

This audit records the substantive repair of PR #8804 at published source
`f100492e57388eacc0eb3a02ba6482183e9cf4b0`, relative to base `829cc48c468ddbce80e8f6d3468ab8e63a6b5dda`.
The graph foundation now has seven production modules and 1202 lines, down from
eight modules and 1422 lines. It exports 43 declarations instead of 50.
The [machine-readable audit](../provenance/evidence/8745/review-fix/api-removal-audit.json)
records the source manifest, all retained signature/body hashes and the removal mapping.

## Retired declarations and exact replacements

All names below are in `TNLean.PEPS.AreaLaw`.

| Removed declaration | Retained replacement |
| --- | --- |
| `card_le_square_of_latticeL1Distance_le` | `card_le_diamond_of_latticeL1Distance_le` |
| `card_le_square_of_walks` | `card_le_diamond_of_walks` |
| `card_le_square_of_edist_le` | `card_le_diamond_of_edist_le` |
| `card_support_le_square` | `card_support_le_diamond` |
| `card_supports_containing_le_square` | `card_supports_containing_le_diamond` |
| `sum_supportWeights_containing_le_square` | `sum_supportWeights_containing_le_diamond` |
| `interactionChainWeightSum_le_lattice_pow` | `interactionChainWeightSum_le_diamond_pow` |

The replacements use the exact ambient count `1 + 2 * R * (R + 1)` instead of
the weaker containing-square count `(2 * R + 1)^2`. The support-count, weight
and chain bounds consequently use the exact count too. These retained results
already existed; the repair removes the redundant family and its blueprint nodes.
`GraphInteractionCounting.lean` and `GraphLatticeCounting.lean` are deleted.

The five `latticeL1Distance` declarations move to `GraphLatticeDistance.lean`.
Their signatures, bodies and active variable context are unchanged. All 43
retained declaration signatures and bodies match the base after comment removal
and whitespace normalization. This is a lexical source comparison, supplemented
by the native/strict compilation below; it is not a separate elaborated-type comparison.

No retired declaration name remains in non-`Archive` production Lean, consumer
Lean or current blueprint source, and no deleted module remains imported there.
This follows the repository's [removal policy](../project_conventions.md#style-mathlib_style):
migrate current uses and cite the replacement without preserving dead aliases.
Historical logs, queries, manifests and dated audits retain their original names
and counts because they describe earlier source revisions.

## Source scope

The source is the September 24 manuscript at
[openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a).
Its [exact ball count](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/01-preliminaries.tex#L81-L87)
is the geometric input. The
[scalar series passage](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/03-quasilocal.tex#L94-L116)
occurs inside the proof of graph-distance propagation, Lemma 4.1. Physical
commutator recursion precedes it; identification with the dynamics, remainder
control and localization are needed for the whole lemma.

The blueprint now describes the proved scalar chain-series statement as that
ingredient. These graph/counting results do not complete the physical propagation
lemma, the area law or the PEPS approximation theorem. All retained ledger rows
remain original formalizations, with no upstream Lean proof text reused.

## Verification and provenance

The [validation record](../provenance/evidence/8745/review-fix/validation.json)
preserves actual run revisions separately from the public source binding:

- Native `TNLean.PEPS.AreaLaw` build: 2880 jobs, exit 0 at local checkpoint
  `d975c515fdebefb092325f9fe6c4d7b50dc9daac`.
- The two changed production files and all five final consumer files pass
  strict compilation at that checkpoint, including `warningAsError`.
- The [raw query](../provenance/evidence/8745/review-fix/axioms.lean) passed at
  `9d7b066236feef96c100ef6cc0efee1e0414f260` and reports all 43 retained declarations:
  34 use the three standard foundational axioms, six use `propext` and `Quot.sound`,
  two use only `propext`, and one is axiom-free. Its 43 informational
  `linter.hashCommand` messages are preserved verbatim; the run exited 0 and
  emitted no warning diagnostics. Permanent consumer guards cover all 43 names.
- Every checked source scope and dependency-pin file is byte-identical to the
  public source revision. The records do not claim the local checks ran at a
  different commit, and preserve raw-output, exported-log and receipt hashes.
- The current full repository provenance validator passes with the pinned
  upstream Git objects: 194 entries, including the 43 retained rows in shard
  `8745.json`. Only that shard is refreshed. The
  [validator receipt](../provenance/evidence/8745/review-fix/provenance-validation.json)
  records its command and source/evidence hashes.

The proposed provenance-policy deletion in PR #8861 was still open on
2026-10-07 when this repair was prepared; it is not applied speculatively.
Earlier evidence remains unchanged. These checks establish targeted source and
metadata consistency; they do not establish full-root CI or a new full-book render.
