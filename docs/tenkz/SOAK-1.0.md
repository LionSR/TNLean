# tenkz 1.0 release-evidence log

This is the evidence ledger for the 1.0 compatibility campaign. Enforcement is
pending: no entry is valid, and the prefix may still be
corrected through ordinary reviewed pull requests.

After the checker, repository-evidence resolver, tests, and CI wiring land, one
self-referential enforcement-activation pull request changes both normative
`enforcement` values from `pending` to `armed`. In this file it also replaces
`policy_sha256 = "pending"` with the SHA-256 of the exact armed `DESIGN.md`
UTF-8 blob and replaces `armed_by_pr = "pending"` with its own pull-request
reference. The digest is exactly 64 lowercase hexadecimal digits computed from
the raw blob bytes without newline normalization. The pull-request reference
has `pr-ref` form. Let `H` be the activation PR's exact final head. A reviewer
distinct from both its normalized author and `github:lionsr` must have a latest
effective `APPROVED` review on `H` before merge. GitHub must then report the PR
merged to `main`, with normalized `mergedBy = github:lionsr` and
`armed_by_pr` naming that PR. Its integration tree must equal `H`'s tree, the
recorded digest must match the exact armed policy blob in that tree, and the
prefix through the final marker must match `H`. Only that post-validated head
pins the policy and prefix.

While validly armed, later changes preserve the pinned policy and prefix and
append live entry blocks after the marker. A correction is an appended entry;
it never revises, deletes, reorders, or inserts preceding bytes.

The following schema block is normative. A later #5352 slice activates its
machine-checking contract.

```toml tenkz-soak-v1
[soak]
schema = 1
policy = "docs/tenkz/DESIGN.md"
enforcement = "pending"
enforcement_transition = "pending-to-armed"
policy_sha256 = "pending"
armed_by_pr = "pending"
append_only = true
append_only_from = "armed"
ordering_anchor = "freeze-record-pr-merged-at"
ancestry_anchor = "freeze-record-pr-merge-commit"
work_anchor = "work-pr-merged-at"
freeze_tag_pattern = "tenkz-v0.9.PATCH"
freeze_tag_kind = "annotated"
release_tag = "tenkz-v1.0.0"
maintainer_identity = "github:lionsr"
signer_identity_scheme = "github:lowercase-login"
```

The work count, class set, and one-class-per-pull-request rule are read from the
exact `DESIGN.md` policy pinned by `policy_sha256`; this ledger schema does not
duplicate them.

Once armed, the normative blocks in `DESIGN.md` and this file have closed
tables and field sets. Unknown tables or fields are rejected. Changing their
schema requires a policy change before arming; it cannot be smuggled into a
live entry.

## Live block and value grammar

Each live entry is exactly one fenced block labelled
`toml tenkz-soak-entry-v1`. Its TOML document has the single top-level table
`[entry]`; no other root key or nested table is legal. A fence with any other
label is not live.

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
| `record_pr` | `pr-ref`; the pull request that first appends this entry |
| `attempt` | `attempt`; governed by the state sequence below |

The `record_pr` targets `main`, is in this repository, and first introduces
exactly this one entry: its base lacks the entry and its exact final
`headRefOid` appends the complete block without changing any pinned byte or
other live entry. GitHub's normalized `record_pr.author.login` must be a valid
lowercase login; authorship is not copied into a self-declared entry field.

For each kind, the common fields plus that kind's fields below are the exact
allowed set. Missing required fields, fields belonging to another kind,
unknown fields, wrong scalar or list types, duplicate list values, extra root
keys, and nested tables are rejected.

## External evidence

Pull-request and issue references are resolved against this repository, not
against entry prose. GitHub supplies PR authors, bases, targets, final
`headRefOid` values, `mergedAt`, `mergedBy`, `mergeCommit.oid`, changed-review
history, and issue `closedAt` state. GitHub timestamps must parse as RFC 3339
instants and are compared in UTC. A normalized identity is `github:` followed
by the lowercase GitHub login.

An integration commit is exactly GitHub's `mergeCommit.oid`; an entry never
chooses it. Ancestry, parent, tree, tag-object, peeled-commit, and path-diff
claims are checked against the exact fetched Git objects. Author, committer,
and tagger timestamps never determine entry ordering. Missing or null fields,
incomplete pagination, unavailable Git objects, malformed values, and any
GitHub/Git disagreement fail closed. The free-form `evidence` field is
descriptive and cannot replace an external fact.

For a reviewer, the latest effective review is that reviewer's latest
non-dismissed `APPROVED` or `CHANGES_REQUESTED` review by `submittedAt`; it is
effective for a head only when its commit OID equals the PR's exact final
`headRefOid`. A later effective review supersedes an earlier one.

## Attempt state sequence

The first live entry is a `freeze` with attempt 1. A `freeze` is legal only
when no attempt is active: initially, or as the next non-correction entry after
the most recent reset, with attempt equal to the reset attempt plus one. While
an attempt is active, every non-correction entry other than its opening freeze
uses that attempt. A reset targets and closes only the active attempt. Ignoring
corrections, the next entry after a reset is the next attempt's freeze. A
correction may target any earlier entry and uses its target's attempt; it never
opens, closes, or changes the active attempt. No entry follows a successfully
validated sign-off.

Each attempt has exactly one opening freeze. If a merged entry fails a required
post-merge identity, ancestry, tree, or ordering check, `record-invalid` is the
next non-correction record; until that reset lands, no later work or sign-off
can validate.

## Entry kinds

### `freeze`

Required additional fields:

| Field | Type |
|---|---|
| `source_pr` | `pr-ref` |
| `source_sha` | `sha` |
| `freeze_tag_object` | `sha` |
| `freeze_tag` | `tag`, matching `tenkz-v0.9.PATCH` |
| `prerequisites` | `list[issue-ref]`, defined below |
| `evidence` | `text` |

`prerequisites` is the pinned `DESIGN.md` policy's `soak_blocker_chain`
flattened row by row. This file owns no second prerequisite list. `PATCH` is a
non-negative decimal integer and is strictly larger than the previous
attempt's patch number.

Before the entry is proposed, GitHub must report `source_pr` merged to `main`
with `source_pr.mergeCommit.oid = source_sha`. The first attempt's `source_sha`
is a strict descendant of `armed_by_pr.mergeCommit.oid`; a later attempt's
`source_sha` is a strict descendant of the preceding reset record's
`record_pr.mergeCommit.oid`. The annotated tag already exists, has object SHA
`freeze_tag_object`, and peels to `source_sha`.

The freeze's `record_pr` is its attempt-activation pull request. Let `H` be
that PR's exact final `headRefOid`. `source_sha` is an ancestor of `H`, and the
complete Git diff from `source_sha` to `H` is exactly one append to
`docs/tenkz/SOAK-1.0.md`: this freeze block. Candidate CI checks the
self-reference, append-only diff, source pull request, tag, current
prerequisite state, and entry grammar, then reports `freeze-pending`. It cannot
record the future merge SHA or time.

After merge, let `I = record_pr.mergeCommit.oid`. GitHub must report the PR
merged to `main`; `I` must be a strict descendant of `source_sha`; and the Git
tree of `I` must equal the Git tree of `H`. GitHub's verified
`record_pr.mergedAt` is the attempt-activation instant `T`, and `I` is its
ancestry anchor.
Every derived prerequisite must be closed with `closedAt <= T`. A tree, source,
tag, prerequisite, or external-identity mismatch requires a `record-invalid`
reset targeting this freeze. A tagger timestamp may appear in `evidence`, but
it never determines ordering.

### `work`

Required additional fields:

| Field | Type |
|---|---|
| `work_pr` | `pr-ref` |
| `class` | `formalization-or-blueprint` or `rmp-benchmark` |
| `summary` | `text` |
| `evidence` | `text` |

Let `H = work_pr.headRefOid` and `I = work_pr.mergeCommit.oid`, as reported by
GitHub. Let `P` be `I`'s sole parent for a one-parent integration or its first
parent for a two-parent integration, and let `B` be the unique Git merge base
of `H` and `P`. A missing object, zero or more than two integration parents, or
a missing or ambiguous merge base fails closed. The work qualifies exactly
when all of these predicates hold:

- GitHub reports `work_pr` merged to `main`, with non-null final
  `headRefOid`, `mergedAt`, and `mergeCommit.oid`.
- `I` is reachable from `main` and is a strict descendant of the active
  freeze record's integration commit, and the Git tree of `I` equals the Git
  tree of `H`.
- The complete path set changed from `B` to `H` contains neither
  `docs/tenkz/DESIGN.md` nor
  `docs/tenkz/SOAK-1.0.md`.
- After whitespace-only changes are ignored, the complete Git diff from `B`
  to `H` has a nonempty change in the recorded class. The
  `formalization-or-blueprint` class matches `TNLean/**/*.lean`,
  `blueprint/src/chapter/**/*.tex`, or `blueprint/src/appendix/**/*.tex`. The
  `rmp-benchmark` class matches `tests/tenkz/rmp/**/cases/*.tex`.
- `work_pr` is not `armed_by_pr`, a `source_pr`, any entry's `record_pr`, or a
  `work_pr` already named by another entry.
- A reviewer distinct from the normalized `work_pr.author.login` has a latest
  effective `APPROVED` review on the exact final `headRefOid`, submitted before
  `work_pr.mergedAt`.

Glob matching is against slash-separated repository paths; `**` spans zero or
more complete path components. The immutable `B`-to-`H` Git diff, not an
integration's final commit alone or a PR title, label, description, or entry
summary, decides path eligibility.

Let `T` be the active attempt's verified freeze merge time. The work PR's
GitHub `mergedAt` must be strictly later than `T`. A work PR fills only the
single class recorded by its entry, even when its immutable diff contains
eligible changes from both classes. Distinct work entries cannot name the same
work PR. Therefore the two required classes are necessarily evidenced by two
distinct post-freeze pull requests. A policy-, checker-, CI-, or record-only
diff contains no class-eligible change and does not qualify.

An active attempt accepts exactly two `work` entries, one in each policy class.
After both classes are filled, a third `work` entry is invalid. Other pull
requests may merge normally; only these two entries are release evidence.

### `friction`

Required additional fields: `surface` (`tex-api` or `tnlog`), `triage`
(`fix-compatible`, `defer-to-2.0`, or `breaking-required`), `summary` (`text`),
and `evidence` (`text`). `fix-compatible` must receive a later `resolution`
before sign-off. `defer-to-2.0` changes nothing in the active major.
`breaking-required` requires a reset as the next non-correction entry.

### `resolution`

Required additional fields: `friction` (`entry-ref`), `summary` (`text`), and
`evidence` (`text`). It resolves one preceding, unresolved `fix-compatible`
friction entry in the same active attempt. It cannot resolve or reclassify
another triage.

### `reset`

Required additional fields: `cause` (`breaking-required` or `record-invalid`),
`target` (`entry-ref`), `reason` (`text`), and `evidence` (`text`).

For `cause = "breaking-required"`, `target` names an unresolved friction entry
with that triage in the active attempt. For `cause = "record-invalid"`,
`target` names the entry in the active attempt whose externally verified
identity, history, ancestry, tree, or ordering evidence is invalid. In
either case the reset is the next non-correction entry, and a correction cannot
repair the cause.

The reset closes the active attempt. The next freeze has attempt number one
higher, a strictly larger `PATCH`, a new source pull request and SHA, a new
annotated tag name and object, and a new record pull request. Its `source_sha`
must be a strict descendant of this reset's `record_pr.mergeCommit.oid`.

### `correction`

Required additional fields: `target` (`entry-ref`), `summary` (`text`), and
`evidence` (`text`). It adds explanatory evidence to any earlier entry and
cannot alter a compatibility decision, identity, ancestry, tree, merge time,
or other externally ordered fact.

A correction's `attempt` equals its target's attempt, including after that
attempt has reset. It remains historical evidence for that attempt and never
opens, closes, reopens, or changes the current attempt.

### `sign-off`

Required additional fields:

| Field | Type |
|---|---|
| `freeze` | `entry-ref` |
| `source_sha` | `sha` |
| `release_tag` | `tag`, exactly `tenkz-v1.0.0` |
| `reviewer` | `identity` |
| `work_evidence` | `list[entry-ref]` |
| `decision` | the exact string `release` |

`freeze` and `source_sha` must match the active attempt. `work_evidence`
contains exactly the active attempt's two work-entry IDs: one
`formalization-or-blueprint` entry and one `rmp-benchmark` entry. Each work PR
fills only its recorded class, and the work-entry rules make the referenced
work PRs distinct. Values are entry references, not pull-request references.

The sign-off's `record_pr` is the sign-off pull request. Let `H` be its exact
final `headRefOid`. Candidate CI validates `H` and reports
`sign-off-pending`; it cannot invent the future merge time or integration
commit. That approved head already carries the 1.0 package metadata, manual
version, change record, event-format declaration, compatibility tests, and
this sign-off entry.

After merge, GitHub must report that `record_pr` targeted `main`. Let
`I = record_pr.mergeCommit.oid`; `I` must descend from the active freeze
integration, and the Git tree of `I` must equal the Git tree of the approved
`H`. Let `W` be the latest GitHub `mergedAt` among the work PRs named by
`work_evidence`. GitHub's `record_pr.mergedAt` must be later than `W`, and
normalized `mergedBy` must be `github:lionsr`. The entry's reviewer is distinct
from that maintainer and from the normalized record-PR author. That reviewer's
latest effective review must be `APPROVED` on `H`, with `submittedAt > W` and
`submittedAt < record_pr.mergedAt`. There is no further waiting interval:
sign-off can proceed as soon as the class coverage, independent exact-head
approval, and all other predicates hold.

All compatible friction must be resolved, every work predicate must still
hold, and no condition may require a reset. Post-merge validation also
revalidates the pinned policy hash and ledger prefix and every active-freeze
fact: its record integration and start time, immutable annotated tag object and
peel to `source_sha`, source-PR integration, and the current closed state and
`closedAt <= T` of every derived prerequisite. A reopened or reclosed
prerequisite, moved or replaced tag, changed source fact, or pinned-byte
mismatch requires a `record-invalid` reset targeting the active freeze. A
sign-off tree or sign-off-specific external-fact mismatch requires that reset
targeting the sign-off. Neither case is a validated sign-off. After post-merge
validation succeeds, the sign-off is terminal and the annotated
`tenkz-v1.0.0` tag may be created on `I`. The tag must not exist before that
success.

No entry may be appended while `enforcement = "pending"`. The activation slice
under #5352 will add validation commands only after their scripts,
repository-evidence resolver, tests, and CI wiring exist on `main`.

<!-- tenkz-soak-entries: append below only while enforcement=armed -->
