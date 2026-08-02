# tenkz 1.0 soak log

This is the append-only evidence ledger for the 1.0 compatibility soak. The
clock is derived only from entries after the final marker. With no valid
`freeze` entry, no soak is running.

After this file first lands on `main`, every existing byte is immutable. Add a
new entry at the end; never revise, delete, reorder, or insert text. A prose or
evidence correction uses a `correction` entry. A wrong freeze SHA, tag, date,
attempt number, friction triage, or other clock-bearing field requires a
`reset` followed by a new `freeze`; a correction cannot rewrite history.

The following schema block is normative and machine checked.

```toml tenkz-soak-v1
[soak]
schema = 1
policy = "docs/tenkz/DESIGN.md"
append_only = true
minimum_days = 28
normal_work_windows = 4
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
object against the repository and current UTC.

## Entry kinds

### `freeze`

Required additional fields: `freeze_sha`, `freeze_tag_object` (both 40
lowercase hexadecimal digits), `freeze_tag` (`tenkz-v0.9.PATCH`),
`freeze_tagger_utc` (`YYYY-MM-DDTHH:MM:SSZ`), `prerequisites` (the exact six
issue IDs in dependency order), and `evidence` (immutable closure evidence).
The tag must be annotated. Its object SHA, peeled commit, and normalized tagger
timestamp must equal the three recorded values; `date` is the UTC date of that
timestamp. The tag and date cannot be in the future, and the peeled commit must
be reachable from `main`. Create and push the tag before committing this entry.

### `work`

Required additional fields: `work_sha`, `work_committed_utc`, `summary`, and
`evidence`. The SHA must be a commit reachable from `main` and descending from
the freeze commit. Its verified committer timestamp must equal
`work_committed_utc`; `date` is that timestamp's UTC date. Future commits,
unmerged branches, invented SHAs, and synthetic soak exercises do not count.
At sign-off, `work_evidence` references at least one verified entry from each
of the four seven-day windows beginning at the tagger timestamp.

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
increased by one. Its annotated tag name, tag object, and peeled post-fix
commit are new, and the commit descends from the prior freeze. The 28-day clock
begins again from that new date.

### `correction`

Required additional fields: `target`, `summary`, and `evidence`. It references
an earlier entry and adds explanatory or evidence text. It cannot alter a
clock-bearing or compatibility decision.

### `sign-off`

Required additional fields: `freeze`, `freeze_sha`, `release_tag`,
`maintainer`, `reviewer`, `work_evidence`, and `decision = "release"`. The
freeze ID and SHA must match the active attempt, `release_tag` must be the
intended `tenkz-v1.0.0`, `maintainer` must be `github:lionsr`, and `reviewer`
must be a distinct normalized GitHub identity. Current UTC must be at least 28
days after the verified tagger timestamp, and `date` cannot be future-dated or
claim an earlier sign-off. Every first-four-weeks work window must be
represented by verified commits. All compatible friction must be resolved and
the attempt must contain no breaking need. Create the final annotated tag only
after this entry lands on `main`; it points to the sign-off-containing commit.

## Example shape

The example is not a log entry because its fence has a different label.

```toml example-tenkz-soak-entry-v1
[entry]
id = "S1-0001"
kind = "freeze"
date = "YYYY-MM-DD"
author = "github:lionsr"
attempt = 1
freeze_sha = "0123456789abcdef0123456789abcdef01234567"
freeze_tag_object = "89abcdef0123456789abcdef0123456789abcdef"
freeze_tag = "tenkz-v0.9.0"
freeze_tagger_utc = "YYYY-MM-DDTHH:MM:SSZ"
prerequisites = ["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]
evidence = "immutable issue-closure and tag evidence"
```

Run the structural and history checks before appending an entry:

```sh
python3 scripts/test_check_tenkz_policy.py
python3 scripts/check_tenkz_policy.py --base-ref origin/main
```

<!-- tenkz-soak-entries: append below; do not edit preceding bytes -->
