---
name: strict_merge_gate
description: Never suggest merging a PR unless every single review comment is addressed — no exceptions for "low severity"
type: feedback
---

Never suggest merging a PR unless ALL review comments from ALL reviewers (Bugbot, Claude, Copilot, Codex, humans) are fully addressed. A "P3" or "low severity" tag does NOT make it OK to skip.

**Why:** User was burned by merging PRs with unaddressed comments (session 2026-03-23). The protocol in `memories/pr_review_management.md` is explicit: "Every review comment must be addressed before merge."

**How to apply:** When presenting PR status, only mark a PR as "merge-ready" if: (1) CI all green, (2) 0 sorry, (3) 0 unresolved threads across all 3 endpoints (inline, PR-level, reviews), (4) all PR-level comment content has been read and any inline-style feedback embedded in PR-level comments is also addressed. If any item remains, post an actionable fix request instead of suggesting merge.
