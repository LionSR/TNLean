---
name: Blueprint ↔ Lean Sync
description: Weekly workflow to detect blueprint .tex annotations that are out of sync with the Lean source code and open a PR with fixes.
on:
  schedule: weekly on monday
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
    labels: [blueprint, blueprint-sync]
    if-no-changes: "warn"
    expires: 7d
  noop:
  missing-data:
---

# Blueprint ↔ Lean Sync

Keep the blueprint `.tex` annotations (`\lean{}`, `\leanok`) in sync with the actual Lean 4 source code in `TNLean/`.

## Background

This project uses the **leanblueprint** system. Each theorem/definition/lemma in the blueprint `.tex` files (under `blueprint/src/chapter/`) can carry:

- `\lean{FullyQualifiedName}` — links the statement to a Lean declaration.
- `\leanok` — asserts the statement (or proof) has been formalized in Lean.
- `\uses{label1, label2}` — declares dependencies on other blueprint items.

The file `blueprint/lean_decls` lists all declaration names referenced from `.tex` files.

## Goal

Detect and fix mismatches between the blueprint annotations and the Lean source tree, then open a pull request with only those fixes.

## Required process

### Step 1: Run the sync checker

```bash
python3 scripts/blueprint_lean_sync.py --root . --report /tmp/sync_report.json
```

Review the output carefully. It will report:
- Blueprint `\lean{X}` refs whose Lean declaration cannot be found.
- `\leanok` tags on items whose declaration is missing from Lean source.
- Stale entries in `blueprint/lean_decls`.
- Blueprint refs missing from `lean_decls`.

### Step 2: Investigate each mismatch

For each reported issue, determine the root cause:

1. **Renamed declaration**: The Lean decl was renamed but the `.tex` wasn't updated.
   - Search for likely matches: `grep -rn "partial_old_name" TNLean/`
   - Update the `\lean{OldName}` to `\lean{NewName}` in the `.tex` file.

2. **Moved to different namespace**: The declaration moved namespaces.
   - Search broadly: `grep -rn "short_name" TNLean/`
   - Update the fully-qualified name in `\lean{}`.

3. **Deleted declaration**: The Lean declaration was intentionally removed.
   - Remove the `\lean{}` and `\leanok` annotations from the `.tex` file.
   - If the entire blueprint item is obsolete, note it but do NOT delete the math content.

4. **Multi-declaration references**: Some `\lean{}` tags list multiple declarations separated by commas (e.g., `\lean{Foo, Bar}`). Each must be checked individually.

5. **lean_decls drift**: `blueprint/lean_decls` is not tracked in git (it is generated). Regenerate it locally with:
   - Run `python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls`

### Step 3: Verify fixes

After making changes, re-run the sync checker to confirm all issues are resolved:

```bash
python3 scripts/blueprint_lean_sync.py --root . --ci
```

### Step 4: Check for new formalizations

Look at recent commits (last 14 days) that added new Lean declarations:

```bash
git log --since="14 days ago" --name-only --pretty=format: -- 'TNLean/**/*.lean' | sort -u
```

For each new `.lean` file or significantly changed file, check if corresponding blueprint items should gain `\leanok` or `\lean{}` annotations. Specifically:

- If a blueprint item has `\lean{X}` but no `\leanok`, and the Lean declaration `X` now exists and is fully proven (not `sorry`), add `\leanok`.
- If a new Lean declaration matches a blueprint item that has no `\lean{}` yet, add the `\lean{NewDecl}` annotation.

To check for `sorry` in declarations:
```bash
grep -n "sorry" TNLean/path/to/file.lean
```

## Scope rules

- Only modify files under `blueprint/src/chapter/`.
- Do NOT modify Lean source files.
- Do NOT change mathematical content in `.tex` files — only update `\lean{}`, `\leanok`, and `\uses{}` annotations.
- Preserve the existing `.tex` formatting and style exactly.

## Pull request requirements

When you make updates, create a PR that includes:

- A summary table of sync issues found and how each was resolved
- Which `.tex` files were modified
- Whether `lean_decls` was regenerated (it is gitignored; CI generates it)
- The current formalization progress (from the sync checker output)
- The theorem, lemma, or definition labels affected by the changes
- Mathematical descriptions without AI vocabulary or software-process metaphors
- Motivation: which paper or blueprint statement needed synchronization, with
  `.tex` file path, line number, theorem label, and Lean declaration name.

## Safety and quality constraints

- Never add `\leanok` unless you have confirmed the Lean declaration exists AND does not contain `sorry`.
- Never remove mathematical content from `.tex` files.
- When unsure about a rename, prefer leaving the annotation as-is and noting it in the PR description rather than guessing.
- If too many issues exist to safely resolve in one PR, fix the clear cases and note the ambiguous ones.
- If information is missing to make a safe update, call `missing-data`.

**Important**: If no action is needed after completing your analysis, you **MUST** call the `noop` safe-output tool with a brief explanation. Failing to call any safe-output tool is the most common cause of safe-output workflow failures.

```json
{"noop": {"message": "No action needed: blueprint annotations are in sync with Lean source code."}}
```
