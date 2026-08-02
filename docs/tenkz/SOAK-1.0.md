# tenkz 1.0 soak log

This is the evidence ledger for the 1.0 compatibility soak. Enforcement is
pending: no entry is valid, no clock is running, and the prefix may still be
corrected through ordinary reviewed pull requests.

After the checker, repository-evidence resolver, tests, and CI wiring land, one
enforcement-activation pull request changes both normative `enforcement`
fields from `pending` to `armed`. That commit pins every byte through the final
marker as the immutable ledger prefix but starts no clock. While armed, later
changes append live entry blocks only. A correction adds a new entry; it never
revises, deletes, reorders, or inserts preceding bytes.

The following schema block is normative. A later #5352 slice activates its
machine-checking contract.

```toml tenkz-soak-v1
[soak]
schema = 1
policy = "docs/tenkz/DESIGN.md"
enforcement = "pending"
enforcement_transition = "pending-to-armed"
append_only = true
append_only_from = "armed"
minimum_days = 28
normal_work_windows = 4
window_days = 7
window_interval = "half-open-utc"
clock_anchor = "activation-pr-merged-at"
ancestry_anchor = "activation-pr-integration-commit"
work_anchor = "work-pr-merged-at"
required_prerequisites = ["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]
freeze_tag_pattern = "tenkz-v0.9.PATCH"
freeze_tag_kind = "annotated"
release_tag = "tenkz-v1.0.0"
maintainer_identity = "github:lionsr"
signer_identity_scheme = "github:lowercase-login"
```

## Live block and value grammar

Each live entry is exactly one fenced block labelled
`toml tenkz-soak-entry-v1`. Its TOML document has the single top-level table
`[entry]`; no other root key or nested table is legal. An example fence with a
different label is not live.

The scalar and reference types are closed:

| Type | Grammar |
|---|---|
| `entry-id` | `S1-[0-9]{4}` |
| `entry-ref` | an earlier live `entry-id` |
| `pr-ref` | `#[1-9][0-9]*`, naming a pull request in this repository |
| `issue-ref` | `#[1-9][0-9]*`, naming an issue in this repository |
| `sha` | exactly 40 lowercase hexadecimal digits |
| `identity` | `github:lowercase-login` |
| `tag` | a nonempty tag name in the `tenkz-v*` namespace |
| `text` | a nonempty TOML string |
| `attempt` | a positive TOML integer |

A `list[TYPE]` is a TOML array whose elements all have `TYPE`, in stated order,
with no duplicates. Every entry has exactly these common fields:

| Field | Type and rule |
|---|---|
| `id` | `entry-id`; `S1-0001`, `S1-0002`, and so on without gaps |
| `kind` | one of `freeze`, `work`, `friction`, `resolution`, `reset`, `correction`, `sign-off` |
| `author` | `identity` |
| `attempt` | `attempt`; starts at 1 and increases only after a reset |

For each kind, the common fields plus that kind's fields below are the exact
allowed set. Missing required fields, fields belonging to another kind,
unknown fields, wrong scalar or list types, duplicate list values, extra root
keys, and nested tables are rejected.

## Entry kinds

### `freeze`

Required additional fields:

| Field | Type |
|---|---|
| `activation_pr` | `pr-ref` |
| `source_pr` | `pr-ref` |
| `source_sha` | `sha` |
| `freeze_tag_object` | `sha` |
| `freeze_tag` | `tag`, matching `tenkz-v0.9.PATCH` |
| `prerequisites` | `list[issue-ref]`, exactly the six schema prerequisites |
| `evidence` | `text` |

`PATCH` is a non-negative decimal integer. It is strictly larger than the
previous attempt's patch number. Before this entry is proposed, GitHub must
report `source_pr` merged to `main` with integration commit `source_sha`, and
the annotated tag must already exist, have object SHA `freeze_tag_object`, and
peel to `source_sha`.

The entry is appended by a ledger-only draft pull request and names that same
pull request as `activation_pr`. The candidate cannot record its own merge SHA
or time because neither exists yet; those fields are forbidden. Candidate CI
checks the self-reference, append-only diff, source pull request, tag, current
prerequisite state, and entry grammar, then reports `freeze-pending`. It does
not claim that a clock is running.

After merge, GitHub's verified `activation_pr.mergedAt` is the attempt start
`T`, and the pull request's external integration commit is its ancestry anchor.
The validator requires `activation_pr` to target `main`, contain only the new
ledger entry, and report every prerequisite closed with `closedAt <= T`. A tag
timestamp may be quoted inside `evidence`, but it is never clock-bearing.

### `work`

Required additional fields:

| Field | Type |
|---|---|
| `work_pr` | `pr-ref` |
| `summary` | `text` |
| `evidence` | `text` |

GitHub supplies the merge SHA and time; neither is copied into the entry. It
must report `work_pr` merged to `main`, and that integration commit must be a
strict descendant of the active `activation_pr` integration commit. The work
must perform normal blueprint or benchmark work. The source pull request,
attempt-activation pull request, enforcement-activation pull request,
policy-only pull requests, ledger-only pull requests, synthetic exercises,
unmerged branches, and a repeated `work_pr` do not qualify.

Let `T` be the active attempt's verified activation merge time. Window `i` is
the half-open UTC interval `[T + 7i days, T + 7(i+1) days)` for
`i = 0, 1, 2, 3`. Work merged exactly on a boundary belongs to the later
window. `T + 28 days` lies outside the fourth window.

### `friction`

Required additional fields: `surface` (`tex-api` or `tnlog`), `triage`
(`fix-compatible`, `defer-to-2.0`, or `breaking-required`), `summary` (`text`),
and `evidence` (`text`). `fix-compatible` must receive a later `resolution`
before sign-off. `defer-to-2.0` changes nothing in the active major.
`breaking-required` must be followed by a `reset` as the next non-correction
entry.

### `resolution`

Required additional fields: `friction` (`entry-ref`), `summary` (`text`), and
`evidence` (`text`). It resolves one preceding, unresolved `fix-compatible`
friction entry in the same active attempt. It cannot resolve or reclassify
another triage.

### `reset`

Required additional fields: `cause` (`breaking-required` or `record-invalid`),
`target` (`entry-ref`), `reason` (`text`), and `evidence` (`text`).

For `cause = "breaking-required"`, `target` names an unresolved friction entry
with that triage in the same attempt, and the reset is the next non-correction
entry. For `cause = "record-invalid"`, `target` names the entry in that attempt
whose externally verified identity, history, or clock-bearing evidence is
invalid. A correction cannot repair either cause.

The reset closes the attempt. The next non-correction entry is a new `freeze`
with attempt number increased by one, a strictly larger `PATCH`, a new source
pull request and SHA, a new annotated tag name and object, and a new
attempt-activation pull request. Its activation integration commit must be a
strict descendant of the prior activation integration commit.

### `correction`

Required additional fields: `target` (`entry-ref`), `summary` (`text`), and
`evidence` (`text`). It adds explanatory or non-clock evidence to an earlier
entry and cannot alter a compatibility decision, identity, ancestry, merge
time, or other clock-bearing fact.

A correction's `attempt` must equal its target's attempt, including after that
attempt has reset. It remains owned by the closed attempt, does not attach to a
later active attempt, and never reopens the target attempt. Corrections may
appear between a reset and the next freeze; the next non-correction entry must
still be that freeze.

### `sign-off`

Required additional fields:

| Field | Type |
|---|---|
| `signoff_pr` | `pr-ref` |
| `freeze` | `entry-ref` |
| `source_sha` | `sha` |
| `release_tag` | `tag`, exactly `tenkz-v1.0.0` |
| `reviewer` | `identity` |
| `work_evidence` | `list[entry-ref]` |
| `decision` | the exact string `release` |

`freeze` and `source_sha` must match the active attempt. `work_evidence`
contains distinct earlier `work` entry IDs from that attempt, at least one in
each of the four windows; values are entry references, not pull-request
references.

The entry names its own pull request as `signoff_pr`. Candidate CI validates
the final head and reports `sign-off-pending`; it cannot invent the future
merge time or integration commit. The exact final head already carries the 1.0
package metadata, manual version, change record, event-format declaration,
compatibility tests, and this sign-off entry.

After merge, GitHub must report that `signoff_pr` targeted `main`, that its
integration commit descends from the active activation integration commit,
that `signoff_pr.mergedAt >= T + 28 days`, and that normalized
`mergedBy = github:lionsr`. The named reviewer is distinct from that
maintainer. Their latest effective review must be `APPROVED`, target the exact
final `headRefOid`, and have `submittedAt > T + 28 days` and
`submittedAt < signoff_pr.mergedAt`. All compatible friction is resolved, and
the active attempt contains no breaking-required or record-invalid condition.
The sign-off is final. Only after it merges is the annotated `tenkz-v1.0.0`
tag created on the sign-off pull request's integration commit.

## Example shape

The example is not a live entry because its fence has a different label.

```toml example-tenkz-soak-entry-v1
[entry]
id = "S1-0001"
kind = "freeze"
author = "github:lionsr"
attempt = 1
activation_pr = "#NNNN"
source_pr = "#NNNN"
source_sha = "0123456789abcdef0123456789abcdef01234567"
freeze_tag_object = "89abcdef0123456789abcdef0123456789abcdef"
freeze_tag = "tenkz-v0.9.0"
prerequisites = ["#5086", "#4699", "#4162", "#4703", "#4708", "#4163"]
evidence = "immutable source, tag, and prerequisite evidence"
```

No entry may be appended while `enforcement = "pending"`. The activation slice
under #5352 will add the validation commands only after their scripts,
repository-evidence resolver, tests, and CI wiring exist on `main`.

<!-- tenkz-soak-entries: append below only while enforcement=armed -->
