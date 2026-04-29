---
name: Docs & Blueprint Sync
description: Daily workflow to detect repository documentation and blueprint files that are out of sync with recent code changes and open a PR with updates.
on:
  schedule: daily on weekdays
  workflow_dispatch:

permissions:
  contents: read
  issues: read
  pull-requests: read

engine: copilot
strict: true
timeout-minutes: 25

network:
  allowed:
    - defaults
    - github

checkout:
  fetch-depth: 50

tools:
  github:
    toolsets: [default, pull_requests]
  bash:
    - "git status"
    - "git diff --name-only"
    - "git log --name-only --pretty=format:"
    - "git log --oneline"
    - "ls"
    - "find docs -type f"
    - "find blueprint -type f"
    - "find TNLean -type f"
    - "grep -R *"
    - "sed -n *"
    - "python3 *"
  edit:

safe-outputs:
  create-pull-request:
    title-prefix: "doc(blueprint): "
    labels: [documentation, automation]
    if-no-changes: "warn"
    expires: 7d
  noop:
  missing-data:
---

# Docs & Blueprint Sync

Review recent repository code changes and keep documentation in sync.

## Goal

Identify stale documentation and blueprint content and update it in a focused way, then open a pull request with only those updates.

## Scope

Prioritize files under:

- `README.md`
- `docs/`
- `blueprint/`

Use `TNLean/` and recent git history as the source of truth for current implementation status.

## Required process

1. Inspect recent commits (for example, last 7 days or ~30 commits) to understand what changed in Lean source files and project structure.
2. Compare those changes against relevant docs/blueprint sections.
3. Update only documentation that is clearly stale or inconsistent with the current codebase.
4. Keep edits minimal, factual, and specific.
5. Do not modify code files unless required to fix broken docs tooling references (prefer doc-only changes).
6. Ensure all changed files are documentation and/or blueprint artifacts.

## Pull request requirements

When you make updates, create a PR that includes:

- A concise summary of what was out of sync
- Which documentation/blueprint files were updated
- Why those updates were needed based on recent code changes

If no updates are needed, call `noop` with a short explanation of what you checked.

## Safety and quality constraints

- Avoid speculative statements; only document what is supported by repository contents.
- Preserve existing style and structure of the modified docs.
- Keep the PR scoped to documentation synchronization only.
- If information is missing to make a safe update, call `missing-data`.

**Important**: If no action is needed after completing your analysis, you **MUST** call the `noop` safe-output tool with a brief explanation. Failing to call any safe-output tool is the most common cause of safe-output workflow failures.

In GitHub Copilot CLI, the runtime safe-output tools may appear with a `safeoutputs-`
prefix (for example `safeoutputs-create_pull_request`, `safeoutputs-missing_tool`,
`safeoutputs-missing_data`, or `safeoutputs-noop`). Use the exact runtime tool name if the
unprefixed name is unavailable.

Do **not** emit raw JSON as plain text for safe-output tools. Invoke the tool directly with the
required fields instead.

Example no-op invocation:
- Tool: `noop` or `safeoutputs-noop`
- `message`: `No action needed: reviewed recent code changes and documentation/blueprint files are already in sync.`
