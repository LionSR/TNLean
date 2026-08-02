# tenkz 1.0 soak log

This is the evidence ledger for the 1.0 compatibility soak. Enforcement is
pending: no entry is valid, the clock is stopped, and the prefix may still be
corrected through ordinary reviewed pull requests.

After the validator, repository-evidence checks, tests, and CI wiring land, one
activation pull request changes both normative `enforcement` fields to
`active`. That activation commit fixes every existing byte as the immutable
ledger prefix. From then on, add a new entry only at the end; never revise,
delete, reorder, or insert text. A prose or evidence correction uses a
`correction` entry. A wrong freeze SHA, pull request, tag, date, attempt number,
friction triage, or other clock-bearing field requires a `reset` followed by a
new `freeze`; a correction cannot rewrite history.

The following schema block is normative. A later #5352 slice activates its
machine-checking contract.

```toml tenkz-soak-v1
[soak]
schema = 1
policy = "docs/tenkz/DESIGN.md"
enforcement = "pending"
append_only = true
minimum_days = 28
normal_work_windows = 4
window_days = 7
window_interval = "half-open-utc"
clock_anchor = "freeze-pr-merged-at"
work_anchor = "work-pr-merged-at"
required_prerequisites = ["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]
freeze_tag_pattern = "tenkz-v0.9.PATCH"
freeze_tag_kind = "annotated"
release_tag = "tenkz-v1.0.0"
maintainer_identity = "github:lionsr"
signer_identity_scheme = "github:lowercase-login"
```

## Entry envelope

Each entry is one fenced block labelled `toml tenkz-soak-entry-v1`. Blocks are
the only content allowed after the marker. Every entry has these fields:

| Field | Rule |
|---|---|
| `id` | `S1-0001`, `S1-0002`, and so on without gaps |
| `kind` | `freeze`, `work`, `friction`, `resolution`, `reset`, `correction`, or `sign-off` |
| `date` | UTC date in `YYYY-MM-DD` form, never earlier than the preceding entry |
| `author` | normalized `github:lowercase-login` identity |
| `attempt` | positive integer; starts at 1 and increases only after a reset |

The first entry of an attempt is `freeze`. Other entries use the active
attempt. A `sign-off` is final. The validator resolves every recorded Git
object against the repository, every pull request against GitHub's merge
metadata, and elapsed time against current UTC.

## Entry kinds

### `freeze`

Required additional fields: `freeze_pr` (`#NNNN`), `freeze_sha` and
`freeze_tag_object` (both 40 lowercase hexadecimal digits),
`freeze_merged_utc` and `freeze_tagger_utc` (both `YYYY-MM-DDTHH:MM:SSZ`),
`freeze_tag` (matching `tenkz-v0.9.PATCH`), `prerequisites` (the exact six issue
IDs in dependency order), and `evidence` (immutable closure evidence).

`PATCH` is a non-negative decimal integer. GitHub must report `freeze_pr`
merged to `main`, with merge commit `freeze_sha` at `freeze_merged_utc`; `date`
is that timestamp's UTC date. The tag must be annotated and peel to that same
commit. Its object SHA and normalized tagger timestamp must equal the recorded
values. The tagger timestamp cannot precede the trusted pull-request merge time
or lie in the future, but it identifies the tag object rather than starting
the clock. The merge commit must be reachable from `main`. Create and push the
tag before committing this entry.

### `work`

Required additional fields: `work_pr` (`#NNNN`), `work_sha` (40 lowercase
hexadecimal digits), `work_merged_utc` (`YYYY-MM-DDTHH:MM:SSZ`), `summary`, and
`evidence`. GitHub must report `work_pr` merged to `main` with merge commit
`work_sha` at `work_merged_utc`; `date` is that timestamp's UTC date. The SHA
must be reachable from `main`, distinct from the freeze SHA, and a strict
descendant of it. The pull request must perform normal blueprint or benchmark
work. The freeze pull request, ledger-only and policy-only changes, unmerged
branches, invented evidence, and synthetic soak exercises do not count.

Let `T` be the active freeze pull request's verified `mergedAt` timestamp.
Window `i` is `[T + 7i days, T + 7(i+1) days)` for `i = 0, 1, 2, 3`; a pull
request merged exactly on a boundary belongs to the later window. At sign-off,
`work_evidence` references at least one verified entry from each window.

### `friction`

Required additional fields: `surface` (`tex-api` or `tnlog`), `triage`
(`fix-compatible`, `defer-to-2.0`, or `breaking-required`), `summary`, and
`evidence`. `fix-compatible` must receive a later `resolution` before sign-off.
`defer-to-2.0` changes nothing in the active major. `breaking-required` must be
followed immediately by a `reset` referencing that friction entry.

### `resolution`

Required additional fields: `friction`, `summary`, and `evidence`. It may
resolve one preceding, unresolved `fix-compatible` friction entry in the same
attempt. It cannot resolve or reclassify another triage.

### `reset`

Required additional fields: `friction`, `reason`, and `evidence`. It references
the immediately preceding `breaking-required` friction entry and closes the
attempt. The next non-correction entry is a new `freeze` with attempt number
increased by one. Its non-negative `PATCH` is strictly larger than the prior
attempt's; its qualifying pull request, merge SHA, annotated tag name, and tag
object are new; and its merge SHA is a strict descendant of the prior freeze.
The 28-day clock begins again from the new pull request's verified `mergedAt`.

### `correction`

Required additional fields: `target`, `summary`, and `evidence`. It references
an earlier entry and adds explanatory or evidence text. It cannot alter a
clock-bearing or compatibility decision.

### `sign-off`

Required additional fields: `freeze`, `freeze_sha`, `release_tag`,
`maintainer`, `reviewer`, `work_evidence`, and `decision = "release"`. The
freeze ID and SHA must match the active attempt, `release_tag` must be the
intended `tenkz-v1.0.0`, `maintainer` must be `github:lionsr`, and `reviewer`
must be a distinct normalized GitHub identity. Current UTC must be at least
`T + 28 days`, where `T` is the freeze pull request's verified `mergedAt`; the
entry's `date` cannot be future-dated or claim an earlier sign-off. Each of the
first four half-open seven-day windows must be represented by a qualifying
pull request. All compatible friction must be resolved and the attempt must
contain no breaking need. The sign-off-containing commit already carries the
1.0 package metadata, manual version, change record, event-format declaration,
and compatibility tests. Create the final annotated tag only after this entry
lands on `main`; it points to that commit.

## Example shape

The example is not a log entry because its fence has a different label.

```toml example-tenkz-soak-entry-v1
[entry]
id = "S1-0001"
kind = "freeze"
date = "YYYY-MM-DD"
author = "github:lionsr"
attempt = 1
freeze_pr = "#NNNN"
freeze_sha = "0123456789abcdef0123456789abcdef01234567"
freeze_merged_utc = "YYYY-MM-DDTHH:MM:SSZ"
freeze_tag_object = "89abcdef0123456789abcdef0123456789abcdef"
freeze_tag = "tenkz-v0.9.0"
freeze_tagger_utc = "YYYY-MM-DDTHH:MM:SSZ"
prerequisites = ["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]
evidence = "immutable issue-closure and tag evidence"
```

No entry may be appended while `enforcement = "pending"`. The activation slice
under #5352 will add the validation commands after their scripts and CI wiring
exist on `main`.

<!-- tenkz-soak-entries: inactive while enforcement=pending -->
