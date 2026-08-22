# Documentation Files

This directory contains shared convention mirrors, upstream-derived mathlib
guidance, and TNLean-owned project policy. Keep those roles separate.

## Shared convention mirrors

The following files are stamped mirrors of the canonical documents in
[texra-ai/texra-lean-skills](https://github.com/texra-ai/texra-lean-skills)
`docs/`. The body below each mirror header is the shared canonical text:
edit it upstream and re-copy, never locally. TNLean-specific material goes
only in the "Project addendum" section at the end of each file.

- `MATHLIB_doc.md`
- `MATHLIB_naming.md`
- `MATHLIB_pr-review.md`
- `MATHLIB_style.md`
- `PROOF_INTEGRITY.md`
- `prose_style.md`

The mirrored MATHLIB files also track mathlib's own documentation and style
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
- `stale_issue_audit.md`
- `tactic_development.md`
- `tactic_patterns.md`
- `tenkz/`
- `upgrade_4_29.md`

When a TNLean rule concerns Lean docstrings or blueprint prose, put it in
the `prose_style.md` project addendum or in `blueprint_style_guide.md`, not
in a mirrored canonical body.

## Audit memos

- `audits/`

`audits/` collects dated scouting, blocker, and source-faithfulness memos, named
`<YYYY-MM-DD>_<topic>.md`. These are historical working notes rather than
maintained policy; live documents that cite a specific memo link to it by its
`docs/audits/...` path.
