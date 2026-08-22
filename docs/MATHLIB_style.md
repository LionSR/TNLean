<!-- Pointer: the canonical document lives in the lean-conventions skill of
     texra-ai/texra-lean-skills, installed automatically in Claude Code
     sessions by .claude/settings.json (other agents: see the install
     instructions in that repository's README). Only the project addendum
     below is repo-local. -->

# Mathlib Style Conventions

Canonical text: the `lean-conventions` skill —
[MATHLIB_style.md](https://github.com/texra-ai/texra-lean-skills/blob/main/skills/lean-conventions/references/MATHLIB_style.md).
Consult it through the installed skill; do not restate its rules here.

## Project addendum (TNLean)

TNLean exercises the repository-local pass-through exception described in
the deprecation section: a public declaration that merely forwards to an
existing theorem, exposes a bundled-structure field, or names a proof step
now written at the use site may be removed without a transition declaration,
provided all non-`Archive` uses are migrated, no blueprint `\lean{...}` tag
cites the old name, and the PR body plus an audit note name each removed
declaration with its replacement.
