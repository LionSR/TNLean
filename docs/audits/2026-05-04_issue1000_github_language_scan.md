# GitHub prose scan for mathematical language

Issue: #1000
Date: 2026-05-04
Repository state: `origin/main` at `e7ef01f1b`

This audit records a live GitHub scan of issue and pull-request titles and
public prose for the vocabulary listed in #1000 and #999.

## Title conventions

The current open-issue title scan is clean for PR-style prefixes and bracket /
em-dash separator residue:

```bash
gh issue list --repo LionSR/TNLean --state open --limit 200 \
  --json number,title,labels,url |
  jq -r '.[] | select(.title|test("^(formalization|infrastructure|feat|fix|doc|style|ci|chore|refactor)\\("))'

gh issue list --repo LionSR/TNLean --state open --limit 200 \
  --json number,title,labels,url |
  jq -r '.[] | select(.title|test("—|\\[|\\]"))'
```

Both commands returned no rows after the 2026-05-04 live rename pass. The
renamed open issues include the former `formalization(...)` and
`infrastructure(...)` titles, the four `Daily Standup — YYYY-MM-DD` issues, and
the open audit/tracking titles with em-dash separators.

The open pull-request title scan is also clean:

```bash
gh pr list --repo LionSR/TNLean --state open --limit 30 \
  --json number,title,isDraft,reviewDecision,mergeStateStatus,headRefName,url
```

It returned no open pull requests.

## Focused body searches

Focused searches over GitHub issues and pull requests still find the #1000
vocabulary, but many hits are deliberate style-guidance issues or issue bodies
that now point to narrower follow-up issues.

```bash
for term in "live block" "live sector" "exact-live" "one-shot" \
  "physical-label compatibility" "source anchors" "channel-side" \
  "dead proof" "bookkeeping" "wrapper" "pipeline" "endpoint" \
  "raw input" "handoff"; do
  printf '%s\t' "$term"
  gh api -X GET search/issues -f q="repo:LionSR/TNLean \"$term\"" --jq '.total_count'
done
```

Counts on 2026-05-04:

| Term | Hits |
| --- | ---: |
| `live block` | 60 |
| `live sector` | 34 |
| `exact-live` | 20 |
| `one-shot` | 20 |
| `physical-label compatibility` | 11 |
| `source anchors` | 11 |
| `channel-side` | 22 |
| `dead proof` | 37 |
| `bookkeeping` | 73 |
| `wrapper` | 305 |
| `pipeline` | 160 |
| `endpoint` | 143 |
| `raw input` | 3 |
| `handoff` | 15 |

Representative current hits:

- `live block`: #1000 itself, #944, #999, and older cleanup PRs such as #1028
  and #1031.
- `bookkeeping`: #1016, #1000, #1018, and older blueprint cleanup PRs.
- `wrapper`: #785, #190, #784, #239, and #1016.

The high counts therefore should not be read as one remaining bulk edit. They
mix style-guidance text, already-closed cleanup PRs, literal Lean identifiers,
mathematical graph terminology such as PEPS endpoints, and real source-prose
residue tracked by narrower issues.

## Current disposition

- Future-facing templates and workflow guidance are handled by #1002 and PR
  #1158: tracking issues now use GitHub Sub-issues rather than Markdown
  tasklists.
- Current open issue titles are handled under #1003; the live open-title scans
  above now return no rows.
- Lean-source prose residue remains under #1013, #1016, #1017, and the parent
  tracker #1018. Those issues should remain open until their scoped source
  scans are clean.
- Historical closed issue and merged PR prose still contains old wording, but
  the scan shows no single safe bulk rewrite. Closed records should only be
  edited when they are still visible from active trackers or when a narrower
  audit identifies a title/body that misleads current work.

## Recommendation

Close #1000 as the repository-wide GitHub scan. Keep #999 open until the
remaining child issues (#1003 and the Lean-source cleanup trackers) are closed
or explicitly superseded.
