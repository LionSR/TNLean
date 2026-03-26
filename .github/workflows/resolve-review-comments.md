---
name: Resolve Addressed Review Comments
description: When new commits are pushed to a PR, check if bot-authored review comments have been addressed and resolve those threads.
on:
  pull_request:
    types: [synchronize]

permissions:
  contents: read
  issues: read
  pull-requests: write

engine: copilot
strict: true
timeout-minutes: 15

network:
  allowed:
    - defaults
    - github

tools:
  github:
    toolsets: [default, pull_requests]
  bash:
    - "git diff --name-only *"
    - "git log --oneline *"
    - "git show *"
    - "grep -n *"
    - "cat *"

safe-outputs:
  noop:
  resolved-threads:
---

# Resolve Addressed Review Comments

When new commits land on a PR, check whether previously posted bot review comments have been addressed and resolve the satisfied threads.

## Goal

Automatically resolve inline review threads authored by bots (e.g. `github-actions[bot]`, `claude[bot]`, `copilot[bot]`) when the latest push addresses the concern. Never touch threads authored by human reviewers.

## Required process

### Step 1: Get all review threads

Use the GitHub `pull_requests` toolset to fetch review threads on the current pull request. Focus on threads that are:

- **Unresolved** (`isResolved: false`)
- **Authored by a bot** — the first comment's author login ends with `[bot]`

Skip any thread that is already resolved or authored by a human.

### Step 2: Evaluate each unresolved bot thread

For each candidate thread:

1. Read the comment body to understand the concern raised.
2. Identify the file and line the comment targets.
3. Read the current version of that file to see the code at that location.
4. Determine whether the latest changes address the concern:
   - If the code was modified in the area the comment references, check if the specific issue is fixed.
   - If the file/line no longer exists (code was removed or moved), the thread is outdated — resolve it.
   - If the concern is clearly still present, leave the thread unresolved.

**Be conservative**: only resolve a thread if the concern is clearly addressed. When in doubt, leave it open.

### Step 3: Resolve addressed threads

For each thread determined to be addressed, resolve it using the GitHub pull request tools. Post a brief reply on the thread confirming resolution, e.g.: "Addressed in the latest push. Resolving."

### Step 4: Report results

If at least one thread was resolved, call `resolved-threads` with a summary:
- Number of threads resolved
- Number of threads still unresolved
- Brief description of what was resolved

If no threads needed resolution (either none existed or none were addressed), call `noop` with a short explanation.

## Safety and quality constraints

- **Never resolve human-authored threads.** Only resolve threads where the first comment author login ends with `[bot]`.
- **Never post new review comments.** This workflow only resolves existing ones.
- **Be conservative.** Only resolve when the concern is clearly addressed.
- **Do not modify any files.** This is a read-only analysis workflow.

**Important**: You **MUST** call either `resolved-threads` or `noop` when finished. Failing to call a safe-output tool is the most common cause of workflow failures.

```json
{"noop": {"message": "No action needed: no unresolved bot review threads found, or none were addressed by the latest push."}}
```
