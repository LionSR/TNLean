---
name: pr_issue_links
description: PR descriptions must link to the issue they address
type: feedback
---

PR descriptions should always link to the issue they address (e.g. "Closes #123" or "Addresses #123").

**Why:** Makes it easy to trace why a PR exists and auto-closes issues on merge. Without links, issues and PRs drift apart.

**How to apply:** When creating PRs or reviewing codex-generated PRs, ensure the body references the issue number. When posting @codex fix requests on issues, include "link to this issue in the PR description."
