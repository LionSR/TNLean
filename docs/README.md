# Documentation Files

This directory contains TNLean-owned project policy and the TNLean-local
addenda to the shared Lean conventions. The shared convention text itself
is not stored here. Keep those roles separate.

## Shared conventions

The canonical convention documents (Mathlib style, naming, documentation,
PR review, proof integrity, prose style) are the references of the
`lean-conventions` skill in
[texra-ai/texra-lean-skills](https://github.com/texra-ai/texra-lean-skills),
installed automatically through `.claude/settings.json`. Consult the skill
for the shared rules; edits to them belong upstream, and this directory
keeps no copy of the canonical text.

TNLean-specific additions to the shared conventions go only in
[`project_conventions.md`](project_conventions.md), one section per shared
reference.

The MATHLIB references also track mathlib's own documentation and style
conventions; changes reconciling them with mathlib belong upstream too.

## TNLean-owned policy

The following files are maintained by this project and may record TNLean-specific
rules, blueprint conventions, GitHub workflow, and source-faithfulness
requirements.

- `CONTRIBUTING.md`
- `blueprint_style_guide.md`
- `ci-automation.md`
- `counterexamples.md`
- `deploy.md`
- `getting_started.md`
- `paper-gaps/`
- `pr_review_management.md`
- `project_conventions.md`
- `stale_issue_audit.md`
- `tactic_development.md`
- `tactic_patterns.md`
- `tenkz/`
- `upgrade_4_29.md`

When a TNLean rule concerns Lean docstrings or blueprint prose, put it in
the prose section of [`project_conventions.md`](project_conventions.md) or
in `blueprint_style_guide.md`; shared rules belong upstream in the skill.

## Audit memos

- `audits/`

`audits/` collects dated scouting, blocker, and source-faithfulness memos, named
`<YYYY-MM-DD>_<topic>.md`. These are historical working notes rather than
maintained policy; live documents that cite a specific memo link to it by its
`docs/audits/...` path.
