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

## Round 2 fixes (continuation session)

A second pass addressed the remaining issues from holistic scouts of chapters 13--16.

### Audits performed (parallel codex scouts)
Five parallel codex agents audited ch13, ch13b, ch14, ch15, and `\notready`→`\leanok`
upgrade eligibility against the actual Lean source code. Reports saved in:
- `ch13_lean_audit.md`, `ch13b_lean_audit.md`, `ch14_lean_audit.md`, `ch15_lean_audit.md`
- `notready_upgrade_audit.md`

### Changes applied

**ch06_spectral.tex**
- Added `\notready` to 3 Wedderburn theorems (all sorry in Lean)

**ch11_assembly.tex**
- Upgraded Periodic FT theorem from `\notready` → `\leanok` (all 4 Lean declarations sorry-free)

**ch12_semigroup.tex**
- Upgraded `irreducible_semigroup_implies_primitive` and `qds_irreducible_iff_primitive` from `\notready` → `\leanok`

**ch13_algebraic_ft.tex**
- `physRealize_mul`: removed unnecessary basis hypothesis (Lean proves for all injective)
- `virtual_bond_gauge`: added Lean-mismatch remark (Lean is 3-site only), added $D \ge 1$
- `fundamentalTheorem_blockedChain`: added remark about blocked-chain vs original-site mismatch
- `chainCombinedTensor_isInjective`: annotated with Lean object note
- Added $D \ge 1$ to `sameMPV_of_sameMPVFrom_of_injective` and `fundamentalTheorem_singleBlock_finiteLength`

**ch13b_symmetry.tex**
- Replaced `U(1)` → `$\C^\times$` in cocycle/cohomology section (matches Lean `Units ℂ`)
- Added Lean-mismatch remarks to `LocalSymmetry` and `HasStringOrder` definitions
- Added missing hypotheses (normalized transfer map, PosDef fixed point, unitary $u$) to 6 string-order theorems
- Fixed proof sketch at line ~801 to mention Kraus freedom (the actual mechanism)
- Added $D \ge 1$ to `cohomologousTo_of_isInjective`

**ch14_parent_hamiltonian.tex**
- Added remark about injective-only Lean scope for `chainGroundSpace_eq_mpvSubmodule`
- Added symmetry hypothesis $c_{ij} = c_{ji}$ to martingale criterion
- Split `gs_eq_bnt_span` into inclusion lemma + equality theorem with correct `\lean{}` tags
- Added remark about `\ker(H_N)` vs `chainGroundSpace` formulation difference
- Added $D \ge 1$ to 6 theorems matching Lean `[NeZero D]`

**ch15_correlations.tex**
- `connectedCorrelator_eq_sum`: `\leanok` → `\notready` with Lean status remark (wrapper lemma)
- `connectedCorrelator_bound`: `\leanok` → `\notready` with Lean status remark (wrapper lemma)
- ZCL remark softened to note spectral equivalence not yet formalized

## Files modified in PR #507

PR `#507` was the vehicle for these blueprint updates.

## Outcome summary

At the end of the session:

- all reviewed must-fix mathematical issues were corrected,
- the known reviewer false positive was documented rather than propagated,
- blueprint prose was cleaned to remove Lean-specific and process-specific language,
- theorem readiness markers were corrected where proofs were absent,
- Lean/blueprint status was re-synchronized without touching the Lean sources,
- `\notready` → `\leanok` upgrades verified transitively sorry-free via `#print axioms`,
- statement-Lean mismatches in ch13/ch13b/ch14/ch15 documented and either fixed or remarked, and
- all 5 audit reports archived in `blueprint/comments20260407/`.
