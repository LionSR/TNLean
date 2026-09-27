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

### Mathlib structures before local ones

Group cohomology (SPT 2-cocycles, anomaly 3-cocycles, L-symbols), projective
representations, coalgebras, bialgebras and Hopf algebras, monoidal and
fusion categories, and fusion rings are built on Mathlib's structures, not on
local parallels. When Mathlib has the notion, TNLean deletes its own
definition and states every downstream declaration on Mathlib's type; it
keeps no parallel type and no bridge or equivalence lemmas between the two.
When Mathlib lacks the notion, TNLean adds the thinnest layer over the closest
Mathlib class, stated so that the standard case is literally Mathlib's
instance. Tracker: #8315.

### Toolchain and Mathlib upgrades

Every Lean/Mathlib bump ships a dated replacement audit,
`docs/audits/<date>_mathlib_<version>_replacement_audit.md`, covering the Mathlib
range from the old pin to the new one. Besides local lemmas that new Mathlib
declarations replace, each audit rechecks Mathlib's coverage of the areas in
the previous subsection:
- group cohomology: a multiplicative degree-3 API, universe polymorphism,
  projective representations, twisted group algebras, and the comparison of
  circle-valued with complex-unit coefficients;
- weak and pre-bialgebras, and C\*-structures on Hopf algebras;
- pivotal, spherical, fusion and module categories, and Frobenius–Perron
  dimensions;
- fusion (based) rings and NIM-reps.

Every local layer that Mathlib has since covered is then migrated in the bump PR
or in an immediate follow-up, by deleting the local definition as above.

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
