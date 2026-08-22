<!-- Pointer: the canonical document lives in the lean-conventions skill of
     texra-ai/texra-lean-skills, installed automatically in Claude Code
     sessions by .claude/settings.json (other agents: see the install
     instructions in that repository's README). Only the project addendum
     below is repo-local. -->

# Prose Style

Canonical text: the `lean-conventions` skill —
[prose_style.md](https://github.com/texra-ai/texra-lean-skills/blob/main/skills/lean-conventions/references/prose_style.md).
Consult it through the installed skill; do not restate its rules here.

## Project addendum (TNLean)

- The designated migrated docstring region is `TNLean/MPS/ParentHamiltonian`:
  inline mathematics there uses `\(...\)`, never backtick code spans.
- The formula-completeness rule bites hardest in the MPS canonical-form and
  fundamental-theorem chapters; prose there must carry the full formulas and
  tuples, not name them away.
