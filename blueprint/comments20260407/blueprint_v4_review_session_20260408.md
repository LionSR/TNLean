# Blueprint v4 Review Session — April 8, 2026

This memory records the blueprint review pass that consolidated review findings, resolved must-fix issues,
and brought the blueprint text back into alignment with the current Lean development. The session was a
blueprint-only cleanup and correction pass: no Lean code was modified.

## Reviews processed

The following review documents were processed during this session:

- `blueprint_chapter5_v4_review.md` (Ch5 Quantum Channels)
- `blueprint_chapter7_v4_review.md` (Ch7 Schwarz/Multiplicative Domains)
- `blueprint_chapter8_v4_review.md` (Ch8 Perron-Frobenius)
- `blueprint_chapter9_v4_review.md` (Ch9 Spectral Gap)
- `blueprint_chapter18_v4_review.md` (Ch18 Parent Hamiltonians)

Source location for the review artifacts:

- `blueprint/comments20260407/blueprint_chapter5_v4_review.md`
- `blueprint/comments20260407/blueprint_chapter7_v4_review.md`
- `blueprint/comments20260407/blueprint_chapter8_v4_review.md`
- `blueprint/comments20260407/blueprint_chapter9_v4_review.md`
- `blueprint/comments20260407/blueprint_chapter18_v4_review.md`

## Critical bugs found and fixed

Three substantive mathematical or expository bugs were identified as must-fix and were corrected in the
blueprint.

1. **Ch9 Thm 9.16 gauging exponents swapped**
   - The blueprint had the gauging written as `ρ^{1/2} A ρ^{-1/2}`.
   - The correct expression is `ρ^{-1/2} A ρ^{1/2}`.
   - The Lean development already had the correct convention; the mismatch was blueprint-only.
   - This was on the fundamental-theorem critical path, so fixing it was high priority.

2. **Ch5 Thm 5.68 wrong exponent**
   - The blueprint stated `|det U|^{2d²}`.
   - The correct exponent is `|det U|^{2D}`.
   - The Lean code confirmed the original formal statement and exposed the blueprint typo.

3. **Ch9 Thm 9.28 irreducibility does not imply spanning**
   - The proof incorrectly claimed that irreducibility implies the family `{B'^i}` spans `M_D`.
   - That spanning conclusion corresponds to injectivity, not mere irreducibility.
   - The argument was repaired by replacing the invalid spanning step with the correct
     kernel-invariance argument.

## Reviewer error documented

One review comment was itself incorrect and was preserved as a documented reviewer issue rather than turned
into a blueprint change.

- **Ch5 Thm 5.54**
  - The reviewer claimed a dimension-convention error.
  - The Lean development confirms that the original blueprint statement was already correct.
  - This was documented in `reviewer_issue_thm554_dimension.md`.

Artifact:

- `blueprint/comments20260407/reviewer_issue_thm554_dimension.md`

## Systematic cleanup performed

Beyond point fixes, the session included a broad language and presentation cleanup across the blueprint.

- Eliminated all Lean jargon from prose, including terms such as `rotatePhysical`,
  `HasInvariantProj`, `IsPrimitiveMPS`, `dysonTerm`, and `gaugeVertex`.
- Replaced `predicate` with `conditions` throughout the affected text, about 25 occurrences across
  Chapters 8 and 9.
- Replaced `CFII data` with `left-canonical normalization` in Chapter 8.
- Replaced `zero tail` and `live blocks` with `trivial block` and `nontrivial blocks` in Chapter 8.
- Renamed five section titles using terms like `infrastructure` or `declarations` so they now use
  mathematical names.
- Removed process-oriented and status-oriented prose such as `not yet formalized`, `upstream`,
  `downstream`, and `pipeline`.
- Added `\notready` to 10 proofless theorems:
  - 4 in Chapter 14
  - 6 in Chapter 13 PEPS
- Fixed malformed theorem/proof nesting in Chapter 15.

The main objective of this cleanup was to make the blueprint read as mathematics rather than as a mixed
mathematics-and-implementation document.

## Quality scout coverage

Review coverage was broad rather than isolated to the five processed review files.

- 9 parallel quality scouts were run across 10 chapters.
- Roughly 158 issues were identified in total.
- All must-fix items from that scout pass were addressed in this session.
- Remaining issues were lower-priority items, mainly proof expansions and notation normalization.

## Lean-blueprint consistency

The consistency pass established the following:

- All `\leanok` tags were checked against the actual Lean sorry status and made consistent.
- No Lean code changes were needed or made.
- The gauging exponent mismatch in Ch9 Thm 9.16 existed only in the blueprint; the Lean proof already
  used the correct statement.

This session should therefore be understood as a documentation-and-blueprint correction pass, not a formal
development pass.

## Files modified in PR #507

PR `#507` was the vehicle for these blueprint updates.

- 14 or more files modified
- 6 commits
- Net diff: `+861/-157`

## Outcome summary

At the end of the session:

- all reviewed must-fix mathematical issues were corrected,
- the known reviewer false positive was documented rather than propagated,
- blueprint prose was cleaned to remove Lean-specific and process-specific language,
- theorem readiness markers were corrected where proofs were absent, and
- Lean/blueprint status was re-synchronized without touching the Lean sources.
