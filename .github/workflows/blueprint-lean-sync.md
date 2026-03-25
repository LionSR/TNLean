---
name: Blueprint ↔ Lean Sync
description: Daily check that blueprint annotations match the Lean source, with a PR for any fixes.
on:
  schedule: daily on weekdays
  workflow_dispatch:

permissions:
  contents: read
  issues: read
  pull-requests: read

engine: copilot
strict: true
timeout-minutes: 30

network:
  allowed:
    - defaults
    - github

tools:
  github:
    toolsets: [default, pull_requests]
  bash:
    - "git status"
    - "git diff --name-only"
    - "git log --name-only --pretty=format:"
    - "git log --oneline"
    - "ls"
    - "find blueprint -type f"
    - "find TNLean -type f -name *.lean"
    - "grep -rn *"
    - "sed -n *"
    - "python3 *"
    - "wc -l *"
    - "cat *"
  edit:

safe-outputs:
  create-pull-request:
    title-prefix: "[blueprint-sync] "
    labels: [blueprint, automation]
    if-no-changes: "warn"
    expires: 7d
  noop:
  missing-data:
---

# Blueprint ↔ Lean Sync

Verify that every `\lean{Name}` and `\leanok` annotation in the blueprint `.tex` files corresponds to an existing declaration in `TNLean/`, and vice versa.

## Context

The blueprint (under `blueprint/src/chapter/`) is a mathematical document whose theorems, definitions, and lemmas carry annotations linking them to their Lean counterparts:

- `\lean{Name}` — the fully-qualified Lean declaration for this statement.
- `\leanok` — this statement (or its proof) has a complete Lean formalization.
- `\uses{label1, label2}` — dependency on other blueprint items.

The file `blueprint/lean_decls` lists every declaration name referenced across all `.tex` files.

## Goal

Find and fix annotation mismatches, then open a PR with the corrections.

## Process

### Step 1 — Run the sync checker

```bash
python3 scripts/blueprint_lean_sync.py --root . --report /tmp/sync_report.json
```

This reports:
- `\lean{X}` references with no matching declaration in `TNLean/`.
- `\leanok` on items whose declaration does not exist.
- Stale or missing entries in `blueprint/lean_decls`.

### Step 2 — Diagnose each mismatch

For every broken reference, determine the cause:

1. **Renamed declaration.** Search for the new name (`grep -rn "old_name" TNLean/`) and update `\lean{}`.
2. **Moved namespace.** Search broadly and update the qualified name.
3. **Removed declaration.** Strip the `\lean{}` and `\leanok` tags. Do not delete the mathematical content.
4. **Comma-separated references** (e.g. `\lean{Foo, Bar}`). Check each name individually.
5. **`lean_decls` drift.** If the `.tex` refs are correct, regenerate via `python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls`.

### Step 3 — Verify

```bash
python3 scripts/blueprint_lean_sync.py --root . --ci
```

### Step 4 — Check for newly formalized results

Inspect recent commits (last 7 days) for new or completed Lean declarations:

```bash
git log --since="7 days ago" --name-only --pretty=format: -- 'TNLean/**/*.lean' | sort -u
```

- If a blueprint item has `\lean{X}` but no `\leanok`, and the declaration `X` now exists without `sorry`, add `\leanok`.
- If a new declaration corresponds to an un-annotated blueprint item, add `\lean{NewDecl}`.

Verify no `sorry` remains:
```bash
grep -n "sorry" TNLean/path/to/file.lean
```

## Scope

- Only modify `blueprint/src/chapter/*.tex` and `blueprint/lean_decls`.
- Do not modify Lean source files.
- Do not alter mathematical content — only annotations.

## PR contents

- Table of mismatches found and how each was resolved.
- List of modified `.tex` files.
- Current formalization progress (from the checker output).

## Constraints

- Never add `\leanok` unless the declaration exists and contains no `sorry`.
- Never remove mathematical statements or proofs from `.tex` files.
- When a rename is ambiguous, leave the annotation unchanged and note it in the PR.
- If there are too many issues for one PR, fix the clear cases and list the rest.
- If you lack enough information, call `missing-data`.

**Important**: If everything is already in sync, you **must** call `noop`:

```json
{"noop": {"message": "All blueprint annotations match the Lean source."}}
```
