---
on:
  schedule:
    - cron: "0 8 * * 1-5"
  workflow_dispatch:

permissions:
  contents: read
  issues: read
  pull-requests: read

tools:
  github:
    mode: remote
    toolsets: [default]

network: defaults

safe-outputs:
  create-issue:
    max: 1
---

# Daily repository activity report

Create a daily repository activity report and publish it as a new issue.

## Scope

Focus on activity in the last 24 hours in this repository.

## Required sections

1. **New issues**
   - List issues opened in the last 24 hours.
   - Include issue number, title, author, and URL.

2. **Pull requests merged**
   - List pull requests merged in the last 24 hours.
   - Include pull request number, title, merged-by (if available), and URL.

3. **Open blockers**
   - Identify open items that indicate a blocker, including:
     - issues labeled `blocker` or `blocked`
     - pull requests labeled `blocker` or `blocked`
   - Include number, title, label(s), current state, and URL.

## Output requirements

- If a section has no items, explicitly write `None`.
- Keep the report concise and easy to scan.
- Use this issue title format: `Daily Activity Report: YYYY-MM-DD` (UTC date of run).
- Publish exactly one issue with the report body using safe output `create-issue`.
