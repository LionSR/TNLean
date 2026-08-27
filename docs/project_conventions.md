# TNLean-local convention addenda

The canonical convention documents live in the `lean-conventions` skill of
[texra-ai/texra-lean-skills](https://github.com/texra-ai/texra-lean-skills)
(auto-installed for Claude Code sessions via `.claude/settings.json`; other
agents: `npx skills add texra-ai/texra-lean-skills`). This file holds only
TNLean's project-local facts — it restates no shared rule, and shared rules
never move here.

## Style (MATHLIB_style)

TNLean does not promise a stable public Lean API. A declaration may be removed
without a deprecation or transition period when all non-`Archive` uses are
migrated, no blueprint `\lean{...}` tag cites the old name, and the PR body plus
an audit note name the removed declaration and its replacement. This local
policy applies to definitions, structures, abbreviations, and theorems alike;
do not retain an otherwise dead declaration solely as a compatibility alias.

## Proof integrity (PROOF_INTEGRITY)

### Sanctioned-axiom history

There are no sanctioned axiom declarations in this repository; any new
`axiom` declaration is a blocker. The one historically sanctioned axiom
(`hayashi_ssa_equality_characterization_forward`, issue #632 / gate #236)
was discharged as a theorem and its modules moved to the
[QICLean](https://github.com/LionSR/QICLean) companion library in the
quantum-channel extraction; QICLean's copy of this document records that
history in its own addendum.

## Prose (prose_style)

- The designated migrated docstring region is `TNLean/MPS/ParentHamiltonian`:
  inline mathematics there uses `\(...\)`, never backtick code spans.
- The formula-completeness rule bites hardest in the MPS canonical-form and
  fundamental-theorem chapters; prose there must carry the full formulas and
  tuples, not name them away.
