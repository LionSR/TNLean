# Stale Issue Audit

The stale-issue audit (`scripts/audit_stale_issues.py`) scans open GitHub issues
for citations that may have drifted out of sync with the current state of the
repository. It is **report-only** — it never edits, closes, or comments on
issues. Flagged items are triage signals for a human maintainer, who decides
whether the citation is genuinely stale or the issue body just needs updating.

## What the audit checks

For each open issue, the audit scans its body for three categories of citation
and checks each against the current `main` branch:

1. **`TNLean/**/*.lean` file paths.** A path that no longer exists on `main` is
   flagged as a *missing file* (e.g., a file that was renamed, moved, or
   removed).

2. **Line-number citations.** When an issue body cites a file together with a
   line number — either with the `file.lean:LINE` suffix or the separate
   `` line NNN `` idiom — the audit checks whether that line still contains a
   `sorry` or `admit`. A line is flagged when:
   - the line exists but no longer has `sorry`/`admit` (someone filled the
     proof), or
   - the line number is past the end of the file (the file was shortened).
   Single-line `--` comments are stripped before matching, so a commented-out
   `-- sorry` does not count as an active sorry site.

3. **Backtick-quoted declaration names.** A token like `` `someLemma` `` that
   looks like a Lean identifer is checked against the set of `def`, `theorem`,
   `lemma`, `structure`, `instance`, `class`, `abbrev`, `inductive`, and
   `opaque` declarations currently present in `TNLean/`. A declaration is
   flagged when it cannot be resolved at all — neither by short name nor by
   namespace-qualified name. Common English words and Lean keywords (e.g.,
   `sorry`, `main`, `simp`, `Nat`) are excluded by a built-in stoplist.

GitHub blob URLs of the form
`https://github.com/OWNER/REPO/blob/REF/TNLean/...` are automatically
normalized to plain `TNLean/...` citations before scanning.

## Report-only contract

The audit tool **never writes to GitHub**. It reads exported issue JSON (produced
by `gh issue list --json ...`) and writes analysis output to stdout or to a
local file. The CI workflow summarises the results and uploads them as artifacts,
but does not modify issue bodies, close issues, or post comments. Every flag is
a suggestion for human review.

## Running the audit locally

First export open issues with the GitHub CLI:

```bash
gh issue list \
  --repo OWNER/REPO \
  --state open \
  --limit 500 \
  --json number,title,body,url,labels \
  > open-issues.json
```

Then run the audit:

```bash
python3 scripts/audit_stale_issues.py --issues open-issues.json
```

### CLI options

| Option          | Description |
|-----------------|-------------|
| `--issues PATH` | JSON file from `gh issue list --json number,title,body,url,labels`. Required unless `--self-test` is used. |
| `--repo-root PATH` | Repository root (default: parent of the script's directory). Must contain a `TNLean/` subdirectory. |
| `--format text\|json` | Output format (default: `text`). |
| `--all` | Include non-flagged issues in text reports (default: only flagged issues). |
| `--output PATH` | Write report to a file instead of stdout. |
| `--self-test` | Run a credentials-free smoke test against a synthetic issue. Exits 0 on success. |

### Self-test

The `--self-test` flag runs a smoke test without talking to GitHub:

```bash
python3 scripts/audit_stale_issues.py --self-test
```

It constructs a synthetic issue referencing a bogus file
(`TNLean/Does/Not/Exist.lean:10`) and a bogus declaration
(`` `definitely_not_a_real_declaration` ``), then verifies both are flagged.
Exits 0 if everything works.

## CI workflow

The `.github/workflows/stale-issue-audit.yml` workflow runs the audit
automatically:

- **Schedule:** Every Monday at 08:30 UTC (cron `30 8 * * 1`), aligned with
  the standup window.
- **Manual dispatch:** Supported via `workflow_dispatch`.
- **Permissions:** `contents: read`, `issues: read`. The workflow never pushes
  code or modifies issues.

The workflow pipeline:

1. Checkout `main` and set up Python 3.12.
2. Export all open issues with `gh issue list` (up to 500).
3. Run the audit twice: once with `--format json` (for the summary) and once in
   text mode (for the human-readable log).
4. Summarise the results and write them to the job's step summary.
5. When flagged issues exist, upload the full audit report as a workflow
   artifact (`stale-issue-audit-report`).

## Maintainer triage policy

When the audit flags an issue, a maintainer should:

1. **Read the flagged citations.** Determine whether the issue body is genuinely
   stale (the cited file, line, or declaration no longer matches the current
   codebase) or whether the audit flag is a false positive (e.g., a declaration
   exists but was missed by the index, or a file path is correct but the script
   misinterpreted a prose sentence).

2. **Update the issue body** to keep the mathematical source citation precise.
   A well-maintained citation includes:
   - **Paper or blueprint path** (e.g., `blueprint/src/chapter/ch02_algebra.tex`,
     or the paper arXiv ID and section number)
   - **Line** (the `file.lean:LINE` of the relevant Lean code, or a
     `` line NNN `` reference when the file path is nearby)
   - **Label** (the Lean declaration name, backtick-quoted, e.g.
     `` `someLemma` ``)
   - **Short quotation** or precise paraphrase of the mathematical statement

3. **Close the issue** only when the mathematical work is done or superseded —
   not merely because a citation became stale. Staleness is a triage signal,
   not a reason to close.

4. **Ignore false positives** from the audit. The tool uses conservative
   heuristics; it may flag items that a human would recognise as still valid.
   The audit is an aid, not a gate.

## Updating issue citations

When you update an issue body, keep the source citation block precise and
machine-scannable. Preferred format:

```
- Paper:  arXiv:XXXX.YYYYY §3.2
- Blueprint: blueprint/src/chapter/ch04_canonical.tex (Lemma 4.3)
- Lean:    TNLean/MPS/CanonicalForm/Basic.lean:142 (`someLemma`)
- Statement: "every block-diagonal sector decomposes as ..."
```

This makes the citation both human-readable and auditable by the script.
