# Documentation Files

This directory contains both upstream-derived mathlib guidance and TNLean-owned
project policy. Keep those roles separate.

## Upstream-derived guidance

The following files follow mathlib documentation and style conventions. Do not
add TNLean-specific policy to them. If they need to change, sync or compare them
with the corresponding mathlib source first, then document the reason in the PR.

- `MATHLIB_doc.md`
- `MATHLIB_pr-review.md`
- `MATHLIB_style.md`
- `MATHLIB_naming.md`

## TNLean-owned policy

The following files are maintained by this project and may record TNLean-specific
rules, proof-integrity policy, blueprint conventions, GitHub workflow, and
source-faithfulness requirements.

- `CONTRIBUTING.md`
- `PROOF_INTEGRITY.md`
- `blueprint_style_guide.md`
- `ci-automation.md`
- `counterexamples.md`
- `deploy.md`
- `paper-gaps/`
- `pr_review_management.md`
- `prose_style.md`
- `upgrade_4_29.md`

When a TNLean rule concerns Lean docstrings or blueprint prose, put it in
`prose_style.md` or `blueprint_style_guide.md`, not in the upstream-derived
mathlib files.
