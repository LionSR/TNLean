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
- `tactic_development.md`
- `tactic_patterns.md`

When a TNLean rule concerns Lean docstrings or blueprint prose, put it in
the prose section of [`project_conventions.md`](project_conventions.md) or
in `blueprint_style_guide.md`; shared rules belong upstream in the skill.

## Audit memos

`audits/` keeps only the dated memos that something still cites: a Lean
docstring, a blueprint entry, a paper-gap note, a live document of this
directory, or an open issue. Memos whose findings have landed are removed;
git history keeps them. Name a new memo `<YYYY-MM-DD>_<topic>.md` and cite it
by its `docs/audits/...` path.

`formalization/` holds the scope notes that the glossary, a paper-gap note or
a module docstring cites. `campaign/` holds the data of the hourly campaign
boards (see `campaign/README.md`). `slides/` holds talk sources.
