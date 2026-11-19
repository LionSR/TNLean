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

Process and conventions:

- `CONTRIBUTING.md`
- `getting_started.md`
- `project_conventions.md`
- `blueprint_style_guide.md`
- `glossary.md`
- `counterexamples.md`
- `pr_review_management.md`
- `ci-automation.md`
- `stale_issue_audit.md`
- `deploy.md`
- `blueprint_dependency_graphs.md`
- `openai-math-provenance.md`

Architecture and build:

- `import_structure.md`
- `many_body_circuit_architecture.md`
- `circuit_channel_architecture.md`
- `related_libraries.md`
- `lake_build_cache.md`
- `upgrade_4_29.md`

Proof maintenance:

- `tactic_development.md`
- `tactic_patterns.md`
- `proof_debt.md`
- `proof_debt_ledger.md`

Source faithfulness and working notes:

- `paper-gaps/`
- `formalization/`
- `campaign/`
- `wolf_source_numbering.md`
- `wolf_theorem_numbering_audit.md`

Other material: `slides/` (talk decks), `archive/` (frozen blueprint
volumes), `validation/` (render-validation records).

When a TNLean rule concerns Lean docstrings or blueprint prose, put it in
the prose section of [`project_conventions.md`](project_conventions.md) or
in `blueprint_style_guide.md`; shared rules belong upstream in the skill.

## Audit memos

- `audits/`

`audits/` collects dated scouting, blocker, and source-faithfulness memos, named
`<YYYY-MM-DD>_<topic>.md`. These are historical working notes rather than
maintained policy; live documents that cite a specific memo link to it by its
`docs/audits/...` path.
