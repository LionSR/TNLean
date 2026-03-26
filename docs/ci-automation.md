# CI Automation Workflows

This document describes the GitHub Actions workflows that automate CI fixes, code review, and review-comment resolution using Claude Code.

## Architecture Overview

```
PR push
  │
  ├─► Lean Action CI ──(failure)──► ci-failure-auto-fix ──► _ci-auto-fix-shared
  │
  ├─► Lint blueprint ──(failure)──► blueprint-auto-fix ───► _ci-auto-fix-shared
  │
  ├─► Claude Code Review ──(success)──► pr-review-auto-fix
  │       ▲                                    │
  │       └────── (push triggers new review) ◄─┘   ← fixed-point loop
  │
  └─► @claude mention ──► claude.yml (ad-hoc assistance)
```

### Fixed-Point Iteration

The review workflow implements a convergence loop:

1. A PR push triggers **Claude Code Review**
2. If the PR has the `auto-fix-claude` label, **pr-review-auto-fix** reads the review comments and pushes fixes
3. The push triggers a new review (step 1), repeating until either:
   - No actionable review comments remain (convergence / fixed point)
   - The combined iteration cap (5) is reached

### Safety Mechanisms

- **Iteration cap**: A shared budget of 5 consecutive bot-fix commits across all auto-fix workflows. Commits tagged `[claude-auto-fix]` and `[claude-review-fix]` both count toward this cap.
- **Concurrency groups**: All auto-fix workflows share the group `bot-fix-<branch>` with `cancel-in-progress: true`, preventing parallel fixes on the same branch.
- **Fork guard**: `workflow_run` workflows check `head_repository.full_name == github.repository` to block fork PRs from triggering auto-fix (prevents privilege escalation).
- **Label gate**: The review-fix loop only activates on PRs with the `auto-fix-claude` label. CI-failure and blueprint fixes run unconditionally.
- **Prompt injection mitigation**: CI logs and review comments are sanitized (non-printable characters stripped, fenced code markers broken) and marked as untrusted data in the prompt.

---

## Workflows

### `_ci-auto-fix-shared.yml` (Reusable)

**Trigger**: Called by other workflows via `workflow_call`.

The shared template for CI failure auto-fix. Accepts inputs for the failing SHA, branch, PR number, prompt, allowed tools, and optional Lean plugin configuration.

**Steps**:
1. Checkout the failing commit and attach to the PR branch
2. Count consecutive bot-fix commits; skip if cap (5) reached
3. Set up git identity and optionally the Lean toolchain
4. Fetch CI failure logs via the GitHub API (last 10,000 chars per job, sanitized)
5. Call Claude Code with the failure details and configured prompt/tools

**Key inputs**:
| Input | Description |
|---|---|
| `head_sha` | The commit SHA that failed |
| `head_branch` | The PR branch name |
| `pr_number` | The PR number |
| `setup_lean` | Whether to install the Lean toolchain |
| `claude_prompt` | The prompt describing what to fix |
| `claude_allowed_tools` | Tool allowlist for Claude |
| `plugin_marketplaces` | Plugin marketplace URLs (optional) |
| `plugins` | Plugins to load (optional) |

---

### `ci-failure-auto-fix.yml`

**Trigger**: `workflow_run` on **Lean Action CI** failure.

Calls the shared workflow with Lean-specific configuration:
- Enables Lean toolchain setup
- Loads Lean plugins (`lean@leanprover`)
- Instructs Claude to fix build errors: resolve `sorry`, fix type mismatches, add imports, try alternative tactics
- Commits with `[claude-auto-fix]` prefix

**Permissions**: `contents: write`, `pull-requests: write`, `actions: read`, `issues: write`, `id-token: write`

---

### `blueprint-auto-fix.yml`

**Trigger**: `workflow_run` on **Lint blueprint** failure.

Calls the shared workflow with blueprint-specific configuration:
- Does **not** set up Lean (blueprint is LaTeX-based)
- Does **not** load Lean plugins
- Instructs Claude to fix leanblueprint compilation errors: unresolved references, duplicate labels, malformed LaTeX, plasTeX parse errors
- Allows `pip install leanblueprint plastex` (restricted, not wildcard)
- Commits with `[claude-auto-fix]` prefix

---

### `pr-review-auto-fix.yml`

**Trigger**: `workflow_run` on **Claude Code Review (Lean)** success.

**Label gate**: Only runs if the PR has the `auto-fix-claude` label.

This workflow closes the fixed-point loop. After a review completes, it:

1. Checks the `auto-fix-claude` label via the GitHub API
2. Counts consecutive bot-fix commits (shared cap of 5)
3. Counts review comments from the latest review cycle (timestamp-scoped to `workflow_run.created_at`)
4. If there are actionable comments, fetches them via `github.paginate()` (handles 100+ comments)
5. Sanitizes comment text and passes it to Claude
6. Claude fixes the issues, runs `lake build`, and pushes with `[claude-review-fix]` prefix
7. The push triggers a new review cycle (back to step 1)

**Convergence detection**: If no bot review comments were created after the triggering `workflow_run` started, the workflow logs "Fixed point reached!" and exits.

---

### `claude-code-review.yml`

**Trigger**: `pull_request` events (`opened`, `synchronize`, `ready_for_review`, `reopened`) on Lean/blueprint files.

**Concurrency**: Per-PR (`claude-review-<PR number>`), cancels in-progress reviews on new pushes.

Runs an automated code review focused on:
- Proof correctness and `sorry` usage
- Mathlib style and naming conventions
- Type safety, universe issues, coercion problems
- Performance (timeout risks, expensive tactics)
- Modularity (upstreaming potential)
- Documentation coverage

**Thread management**: On `synchronize` events, the review reads existing threads and resolves its own (bot-authored) threads that have been addressed by new commits. Human-authored threads are never resolved.

---

### `claude.yml`

**Trigger**: `@claude` mentions in issue comments, PR review comments, PR reviews, or issue bodies/titles.

**Concurrency**: Per-issue/PR, does **not** cancel in-progress runs.

General-purpose Claude assistant for ad-hoc tasks. Has broad tool access including `lake build`, `gh` CLI, `leanblueprint`, and `mcp__github__*` MCP tools. Instructed to:
- Prefer minimal diffs
- Complete proofs rather than changing theorem statements
- Read existing review threads for context
- Reply directly to the triggering review thread
- **Not** resolve review threads (left to humans or the automated review workflow)

---

## Commit Tags

| Tag | Used by | Meaning |
|---|---|---|
| `[claude-auto-fix]` | `ci-failure-auto-fix`, `blueprint-auto-fix` | Automated CI failure fix |
| `[claude-review-fix]` | `pr-review-auto-fix` | Automated review comment fix |

Both tags count toward the shared 5-iteration cap.

---

## Permissions Matrix

| Permission | ci-failure | blueprint | pr-review | review | claude |
|---|---|---|---|---|---|
| `contents` | write | write | write | read | write |
| `pull-requests` | write | write | write | write | write |
| `actions` | read | read | read | read | read |
| `issues` | write | write | write | write | write |
| `id-token` | write | write | write | write | write |

---

## Configuration

### Enabling the review-fix loop

Add the `auto-fix-claude` label to a PR. The CI-failure and blueprint auto-fix workflows run unconditionally on any PR (no label needed).

### Iteration cap

The maximum number of consecutive bot-fix commits is `5`, defined as `MAX_BOT_FIX_ITERATIONS` in both `_ci-auto-fix-shared.yml` and `pr-review-auto-fix.yml`. If you change this value, update it in both files (cross-referenced via comments).

### Model

All workflows use `claude-opus-4-6`. This is configured in `claude_args` within each workflow.
