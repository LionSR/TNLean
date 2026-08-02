# tenkz 1.0 release-evidence log

This is the evidence ledger for the 1.0 compatibility campaign. Enforcement is
pending: no entry is valid, and the prefix may still be
corrected through ordinary reviewed pull requests.

For orientation, a successful attempt has this shape:

`freeze -> two real-work records -> resolve active friction -> prepare -> sign off -> tag`

Friction may be recorded whenever it appears, and the two work records may land
in either order. There is no clock delay. A breaking change or invalid record
resets the attempt instead of asking the next attempt to inherit its unfinished
business. This map is only a reading aid; the exact rules below decide validity.

Only after the checker, repository-evidence resolver, tests, CI wiring, and
closed test inventory exist on `main`, and the complete blocker chain is closed,
may one self-referential enforcement-activation pull request arm the campaign.
Let `C` be its exact current `main` target and `H` its exact final head. `C` must be an
ancestor of `H` and their unique merge base. The complete `C`-to-`H` diff may
change only `docs/tenkz/DESIGN.md` and this file, and only these seven scalar
values:

- `docs/tenkz/DESIGN.md`: `enforcement` from `pending` to `armed`, the pending
  inventory digest to the inventory blob's SHA-256, and the pending test-code
  tree to the exact Git tree OID of its configured root, and the pending
  test-support tree to the exact Git tree OID of its configured root;
- this file: `enforcement` from `pending` to `armed`, the pending policy digest
  to the resulting armed `docs/tenkz/DESIGN.md` blob's SHA-256, and
  `armed_by_pr` to this pull request's `pr-ref`.

No other byte or path may change. Each digest is exactly 64 lowercase
hexadecimal digits computed from raw blob bytes without newline normalization;
each Git tree OID is exactly 40 lowercase hexadecimal digits. The activation
validator recomputes all four pinned values at `H`, verifies that runner paths
are inside the test-code tree, verifies the declared dependency boundary, and
verifies the prefix through the final marker.

GitHub must report current active protection covering the complete `tenkz-v*`
tag namespace, forbidding updates and deletions and exposing no bypass actor. The
resolver fetches every applicable repository and organization ruleset through
complete pagination. Its credential principal has the write-level ruleset
visibility needed to receive unredacted rule and bypass details, although the
validator performs only read requests. Missing, omitted, redacted, inactive,
weaker, ambiguous, or bypassable protection fails closed.

A repository-authorized reviewer distinct from both the activation PR's
normalized author and the pinned policy's `maintainer_identity` must have a
latest effective `APPROVED` review on `H` before merge. GitHub must then report
the PR merged to `main`,
with normalized `mergedBy` equal to that pinned identity and `armed_by_pr`
naming the PR. Its integration tree must equal `H`'s tree. Only that
post-validated head pins the inventory, test-code tree, test-support tree,
enforcement workflows, policy, and prefix and arms the campaign. Every later
validation rechecks their exact values and the current ruleset state.

The policy's closed enforcement-workflow list names regular Git blobs. Their
exact blob OIDs and modes at the activation integration are pinned through
`armed_by_pr`, not through another editable scalar. Every candidate and
post-merge validation resolves that integration and requires the same blobs and
modes at its exact target; its complete candidate diff may not touch those
paths. A GitHub check result counts only when its exact head and executed
workflow resolve to the pinned bytes. It cannot replace the independent
evidence-supervisor result. A missing, renamed, non-blob, or changed workflow
fails closed.

The resolver closes the dedicated workflow's transitive executable dependency
graph. Each local action or reusable workflow is pinned by its activation Git
object and joins every later byte-and-mode check. Each external action or
reusable workflow reference ends in a full commit SHA, never a tag or branch;
each container ends in a content digest. The same rules recursively cover
composite actions, called workflows, interpreters, helpers, packages, and any
executable fetched at runtime. A package manager, downloader, unhashed lock,
mutable resolution, unavailable object, incomplete closure, or cycle fails
closed. After GitHub materializes the checkout and content-addressed closure,
the job disables network access before repository code, the checker, a helper,
or a validation command runs. GitHub's control plane and hosted runner remain
trusted; downloaded mutable executable content does not.

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
```

The work count, class set, excluded paths, and one-class-per-pull-request rule
are read from the exact `docs/tenkz/DESIGN.md` policy pinned by
`policy_sha256`; this ledger schema does not duplicate them. Tag immutability
and the release manifest, canonical-artifact, inventory, runner, and enforcement-workflow
configuration are likewise read only from that pinned policy, as are the
maintainer identity, signer identity scheme, and authorized reviewer permission
set.

Once armed, the normative blocks in `docs/tenkz/DESIGN.md` and this file have
closed tables and field sets. Unknown tables or fields are rejected. Changing
their schema requires a policy change before arming; it cannot be smuggled into
a live entry.

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
| `sha256` | exactly 64 lowercase hexadecimal digits |
| `identity` | `github:lowercase-login` |
| `tag` | a nonempty tag name in the `tenkz-v*` namespace |
| `test-ref` | the exact `id` of a test in the pinned release-test inventory |
| `text` | a nonempty TOML string |
| `attempt` | a positive TOML integer |
| `entry-kind` | one of the seven entry-kind headings below |

A `list[TYPE]` is a TOML array whose elements all have `TYPE`, in stated order,
with no duplicates. Every entry has exactly these common fields:

| Field | Type and rule |
|---|---|
| `id` | `entry-id`; `S1-0001`, `S1-0002`, and so on without gaps |
| `kind` | `entry-kind` |
| `record_pr` | `pr-ref`; the pull request that first appends this entry |
| `attempt` | `attempt`; governed by the state sequence below |

The `record_pr` targets `main`, is in this repository, and first introduces
exactly this one entry: its base lacks the entry and its exact final
`headRefOid` appends the complete block. Let `H` be that exact head, `C` the
target `main` tip used by candidate validation, and `B` the unique Git merge
base of `H` and `C`. `C` must be an ancestor of `H`, hence `B = C`. The complete
`C`-to-`H` path set and diff must be exactly that one append to
`docs/tenkz/SOAK-1.0.md`: no other file, pinned byte, or live entry changes.
GitHub's normalized `record_pr.author.login` must be a valid lowercase login;
authorship is not copied into a self-declared entry field. Candidate validation
must run on that declared pull request at `H`; copying the block into another
pull request is invalid. Before merge it reports the kind-specific pending
state because the integration facts do not yet exist.

After merge, GitHub must report `record_pr` merged to `main` with non-null
`mergedAt` and `mergeCommit.oid`. Let `I` be that integration commit and `P`
its sole parent for a one-parent integration or first parent for a two-parent
integration. Zero or more than two parents, a missing object, or a missing or
ambiguous merge base fails closed. `P` must be an ancestor of `H`, hence the
recomputed `B = P`; for a two-parent integration, the second parent must equal
`H`. Revalidate the complete ledger-only `P`-to-`H` diff. `I` must be reachable
from `main`, and its Git tree must equal `H`'s tree. These common post-merge
rules apply to every entry kind; the kind-specific rules add their ancestry and
ordering predicates.

For each kind, the common fields plus that kind's fields below are the exact
allowed set. Missing required fields, fields belonging to another kind,
unknown fields, wrong scalar or list types, duplicate list values, extra root
keys, and nested tables are rejected.

## External evidence

Pull-request and issue references are resolved against this repository, not
against entry prose. GitHub supplies PR authors, bases, targets, final
`headRefOid` values, `mergedAt`, `mergedBy`, `mergeCommit.oid`, changed-review
history, issue `closedAt` state, and the complete active repository and
organization ruleset configuration applicable to the tag namespace. GitHub
timestamps must parse as RFC 3339 instants and are compared in UTC. A normalized
identity is `github:` followed by the lowercase GitHub login.

An integration commit is exactly GitHub's `mergeCommit.oid`; an entry never
chooses it. Ancestry, parent, tree, tag-object, peeled-commit, and path-diff
claims are checked against the exact fetched Git objects. Author, committer,
and tagger timestamps never determine entry ordering. Missing or null fields,
incomplete pagination, unavailable Git objects, malformed values, and any
GitHub/Git disagreement fail closed. The free-form `evidence` field is
descriptive and cannot replace an external fact. Ruleset administrators and the
GitHub control plane are trusted. Ruleset validation establishes protection in
the current complete snapshot; it does not claim to detect a temporary
administrator-created gap that was restored before that snapshot.

For a reviewer, the latest effective review is that reviewer's latest
non-dismissed `APPROVED` or `CHANGES_REQUESTED` review by `submittedAt`; it is
effective for a head only when its commit OID equals the PR's exact final
`headRefOid`. A later effective review supersedes an earlier one. A reviewer is
repository-authorized only when the complete current GitHub snapshot's
collaborator-permission response for that normalized login has a top-level
`permission` value in the pinned policy's `reviewer_repository_permissions`.
These are GitHub's legacy base values: `maintain` maps to `write`, while
`triage` maps to `read`; nested `push` and `pull` capability flags are not role
names. Missing, `none`, `read`, or unavailable permission evidence fails closed.

## Release payload evidence

In this ledger, `Q` is either the active attempt's exact 0.9 freeze tag or
`tenkz-v1.0.0`. No later package tag is validated by this campaign. For such a
tag `Q`, substitute the exact tag name for `TAG` in the pinned
policy's `release_manifest_pattern`. The resulting manifest is a regular Git
blob with one `[release]` table and exactly `schema`, `tag`, `version`, `date`,
`test_inventory_sha256`, `test_code_tree`, and `test_support_tree`. `schema` is
integer 1; `tag` equals `Q`; `version` is the numeric version suffix of `Q`;
`date` is an ISO 8601 calendar date; the inventory digest equals the pinned
policy value; and each tree is a 40-digit lowercase Git OID equal to its pinned
policy value.

The package metadata, manual, change record, event-format declaration, and
test-inventory paths come only from the pinned policy, never from the release
manifest or entry prose. They are distinct normalized repository-relative
paths naming regular Git blobs. The package metadata and manual declare the
manifest's version and date. The change record and event-format declaration
name the exact tag and version. Missing paths, symlinks, submodules, duplicate
paths, malformed declarations, or disagreement fails closed.

The inventory is a TOML document with `schema = 1` and one or more `[[test]]`
tables. Each test has exactly `id` (a unique lowercase hyphenated identifier),
`surface` (exactly `tex-api` or `tnlog`), `failure_fingerprint` (a `sha256` value
unique across the inventory), `runner`
(exactly `python3` or `bash`), `path` (a normalized regular file below the
configured test-code root with the matching `.py` or `.sh` suffix), `args` (a
list of nonempty argument strings), `program_paths` (a duplicate-free list of
normalized regular subject blobs beneath the policy's
`release_test_subject_roots`),
`fixture_paths` (a duplicate-free list of normalized subject blobs or trees
beneath those roots), and `timeout_seconds` (a positive integer). Program paths
also lie beneath those subject roots. Program and
fixture paths are disjoint, and no fixture tree may contain a program path.
Every program path matches the fix-path set for the test's one surface.

Each inventory command evaluates exactly one atomic compatibility assertion;
its ID and failure fingerprint cannot represent a suite or multiple failure
causes. The evidence runner executes `[runner, path, *args]` directly, without a
shell expansion or added argument, from the root of the hermetic view below, in
inventory order, and kills it at its declared timeout. Payload validation
requires every command to exit zero. Incomplete execution, a signal, timeout,
unknown field, path escape, or nonzero exit fails closed. The activation
validator recomputes the inventory's raw-blob SHA-256 before arming; every later
payload validation recomputes it and rejects a mismatch.

For each command, the evidence supervisor creates a fresh repository-shaped
filesystem view of `K`. At their original relative paths it exposes read-only
copies of only the pinned code tree, pinned support tree, inventory blob,
tag-derived manifest, canonical artifacts, and that command's declared
`program_paths` and `fixture_paths`. Every exposed repository entry is
recursively a regular blob or tree; symlinks, submodules, and other Git modes are
rejected without following them. The supervisor mounts one empty writable
directory at `/tenkz-output` and sets `TENKZ_TEST_OUTPUT=/tenkz-output`; no
command argument is added. The real checkout, user files, and every other
repository path are absent from the process mount namespace.

The environment has fixed locale and timezone, no inherited repository-path
variables, and no network access. Its sanitized `PATH` contains the inventory
runner and only child tools in an explicit allowlist embedded in the pinned
supervisor. The supervisor resolves each tool without following a repository
link, validates its configured version fingerprint, and records the resolved
identity in the receipt. An undeclared read, import, source, execution, or
repository-tree write fails the command. A test that cannot run under this view
cannot enter the inventory.

Activation runs a closed supervisor self-test suite from the pinned support
tree against pinned synthetic fixtures. Its receipt binds the code and support
trees, output mount, environment, access denials, tool fingerprints, and
completion of every isolation probe. It requires no package tag, release
manifest, canonical payload, or mutable subject. A missing or mismatched
self-test receipt prevents arming.

The configured test-code and test-support roots must be regular Git trees in
`K` whose exact tree OIDs equal their policy and manifest values. Runner code
and every imported, sourced, or executed in-repository helper must come from the
dedicated test-code tree. Expected outputs, baselines, allowlists, thresholds,
selector manifests, and other acceptance-control files must come from the test-support
tree. The payload checker and each test may read only the tag-derived manifest,
canonical artifacts, and its declared program and fixture paths as mutable
subjects. Every canonical artifact that a test reads must also occur in exactly
one of its two declared roles. Only a declared program path may be executed,
sourced, or imported as the product under test through the pinned harness.
Fixture paths remain non-executable. Neither subject role can supply runner, helper,
acceptance-control, or coverage-selection logic. Loading any other repository
file, or using a subject to reduce the inventory-defined checks, fails closed.

On its sole atomic assertion failure, a pinned harness command exits exactly 10
only after atomically writing `/tenkz-output/assertion-failure-v1.json`. That
closed JSON object has exactly four fields: integer `schema = 1`, string
`test_id` equal to the selected inventory test's `id`, its string
`failure_fingerprint`, and Boolean `completed = true`. Exit 10 without that
exact receipt, the receipt with another exit, a second failure cause, or any
other nonzero exit fails closed. The supervisor emits a per-command payload
receipt naming the exact trees, blobs, program paths, fixture paths, command,
assertion result, exit status, timeout result, output mount and environment
value, and child-tool fingerprints. `validate-release-payload(K, Q)` accepts
only assertion passes and rejects any incomplete or mismatched payload receipt.

`validate-release-payload(K, Q)` means checking this complete manifest,
canonical-artifact, pinned-inventory, both pinned test trees, dependency
boundary, and test contract in Git tree `K` for tag `Q`.

`observe-release-test(K, Q, R)` performs those same manifest, artifact,
inventory, pinned-tree, dependency, hermetic-view, and tool checks, then runs
exactly the inventory test with `id = R`. It returns either `passed` for exit
zero or `assertion-failed` for exit 10 with the exact fingerprint receipt above.
A missing test, unrelated nonzero exit, signal, timeout,
incomplete run, isolation failure, or setup mismatch fails closed. This
single-test observation cannot replace `validate-release-payload`; it exists
only to bind a friction's before-and-after regression evidence.

## Attempt state sequence

The first live entry is a `freeze` with attempt 1. A `freeze` is legal only
when no attempt is active: initially, or as the next non-correction entry after
the most recent reset, with attempt one higher than the most recently opened
attempt. While an attempt is active, every non-correction entry other than its
opening freeze uses that attempt. A restart reset targets and closes only the
active attempt. A correction may target any earlier entry and uses its target's
attempt; it never opens, closes, or changes the active attempt. Before the final
tag exists, a required `record-invalid` reset may follow a sign-off. No entry
follows a released sign-off.

Each attempt has exactly one opening freeze. The audit boundary is not an entry
field, timestamp, or caller choice: it is the final live entry in the immutable
ledger prefix at the start of a fail-closed validation against one complete
current GitHub/Git snapshot and exact validation target. The resolver supplies
a closed `AuditEvidence` value containing that `boundary_entry_id`, the
ledger-ordered `invalid_entries` not already acknowledged as defined below,
and true `snapshot_complete` and `validation_target_exact` flags. A caller
cannot choose or weaken those fields. The boundary must equal the actual final
live entry in that prefix; reusing an earlier boundary is invalid.

Historical reset placement and prospective drift use separate evidence
channels. For every merged `record-invalid` reset at or before the boundary,
the resolver reads the reset's named receipt blob at its canonical path from
the exact current validation tree. The raw bytes must match the reset's digest.
The blob uses the closed JSON schema at the pinned policy's
`release_reset_replay_schema`. It binds the reset and target
entry IDs, exact pre-reset ledger boundary, exact validation-target commit,
ledger-ordered raw-invalid queue, `pending_restart_target` (`entry-id` or null),
complete normalized resolver inputs, pinned workflow dependency closure, and independent
supervisor receipts. Unknown or missing data fails closed.

The receipt pull request targets the exact current `main` tip and changes only
one new regular blob at `docs/tenkz/soak-replay/NUMBER.json`, where `NUMBER` is
its own decimal pull-request number. Its author is distinct from an exact-head
approving repository-authorized reviewer; normalized `mergedBy` equals the
pinned maintainer. GitHub
reports it merged to `main`, reachable, with its integration tree equal to its
approved final-head tree. The reset record's candidate base and later
integration parent equal that receipt integration, so its integration tree
contains the same regular receipt blob, mode, and raw bytes. If `main` advances first, a
new receipt pull request is required; a stale receipt is never overwritten.
At reset-candidate validation, a complete current snapshot at that exact base
must reproduce the receipt's queue and still-mutable inputs. A mismatch makes
the receipt stale and requires another receipt pull request.

The reset entry binds the receipt PR and SHA-256 of the raw receipt blob. The
validator reconstructs its historical queue, applies the pending-restart
priority below, and requires the reset to name its head. Receipt-PR reachability,
review, merge, and tree equality are creation predicates rechecked when the
reset first integrates. Every later entry's candidate target, exact head, and
integration must retain every earlier reset's receipt as the same regular blob,
mode, path, and raw digest; its entry diff cannot touch those paths. Later
replay reads the retained blob from the exact current validation tree and does
not require an old receipt integration to remain reachable. An expiring
workflow artifact, check log, or newly supplied historical snapshot cannot
replace it. Missing retained bytes fail closed until the exact digest is
restored at the canonical path. This is not a caller-selected audit boundary.

A historically valid reset acknowledges its target while that reset continues
to pass its own current common, external, and kind-specific checks. The current
resolver forms `AuditEvidence.invalid_entries` from current raw-invalid entries
after subtracting those acknowledged targets. If an acknowledging reset later
fails a current check, its target is uncovered and both the target and reset
are independently included when invalid. Historical replay never substitutes
an earlier prefix for the current boundary, and the final `invalid_entries`
value is not fed back into its own derivation.

When the reset queue is nonempty, the first new non-correction entry after the
boundary is its head. If a `restart-required` reset was already pending at the
boundary, it heads the queue and closes the active attempt; otherwise the queue
starts with the `record-invalid` reset for the earliest invalid entry. Remaining
`record-invalid` targets follow in ledger order, consecutively while the
campaign is inactive; corrections are the only entries that may interleave.
Such a target is any unacknowledged raw-invalid merged entry and may belong to
any attempt. External facts may drift after later
entries already landed; those intervening entries remain historical and do not
make an adjacent reset possible. A record-invalid reset closes the active
attempt if one remains and otherwise uses the most recently opened attempt
while leaving the campaign inactive. Until the ordered reset queue is empty,
no work, freeze, or sign-off can validate. The next freeze is numbered one
higher than the most recently opened attempt, independent of how many
administrative resets landed.

## Entry kinds

### `freeze`

Required additional fields:

| Field | Type |
|---|---|
| `source_pr` | `pr-ref` |
| `source_sha` | `sha` |
| `freeze_tag_object` | `sha` |
| `freeze_tag` | `tag`, matching `tenkz-v0.9.PATCH` |
| `freeze_tag_snapshot` | nonempty `list[tag]`, defined below |
| `prerequisites` | `list[issue-ref]`, defined below |
| `evidence` | `text` |

`prerequisites` is the pinned `docs/tenkz/DESIGN.md` policy's `soak_blocker_chain`
flattened row by row. This file owns no second prerequisite list. `PATCH`
matches the canonical grammar `0|[1-9][0-9]*`. Candidate validation completely
paginates the current Git tag namespace, parses every name matching
`tenkz-v0.9.PATCH`, and requires `freeze_tag_snapshot` to equal that complete
nonempty name set in ascending numeric-patch order. The list includes this
entry's exact `freeze_tag`; annotated and lightweight refs both contribute their
names. This patch must be strictly larger than every other patch in the snapshot
and every earlier freeze entry's patch. A wrong tag kind still fails its separate
check. Thus an abandoned tag with no ledger entry cannot be skipped or followed
by a smaller patch.

Historical replay does not compare an earlier freeze with tags created after
that entry. It requires the successful exact-head candidate check bound to the
pinned workflow bytes and the retained `freeze_tag_snapshot`. The complete
current matching namespace must be a superset of that snapshot. Replay rechecks
the freeze's patch against its retained names and earlier freeze entries, then
revalidates its exact protected annotated tag object and peel. A later attempt's
higher tag therefore cannot make an earlier freeze raw-invalid.

Before the entry is proposed, let `H_S = source_pr.headRefOid`. GitHub must
report `source_pr` merged to `main` with non-null author, `H_S`, `mergedAt`, and
`source_pr.mergeCommit.oid = source_sha`. A repository-authorized reviewer
distinct from the normalized source-PR author must have a latest effective
`APPROVED` review on
the exact `H_S`, submitted before `source_pr.mergedAt`. The Git tree of `source_sha`
must equal the Git tree of `H_S`. The first attempt's `source_sha` is a strict
descendant of `armed_by_pr.mergeCommit.oid`; a later attempt's `source_sha` is a
strict descendant of the preceding reset record's `record_pr.mergeCommit.oid`.
Before tag creation,
`validate-release-payload(source_sha, freeze_tag)` must pass. The annotated tag
then exists, has object SHA `freeze_tag_object`, and peels to `source_sha`. The
target `main` tip `C` from the common candidate rule must equal `source_sha`;
the source integration is therefore the candidate's unique merge base `B`.

The freeze's `record_pr` is its attempt-activation pull request. Let `H` be
that PR's exact final `headRefOid`. `source_sha` is an ancestor of `H`, and the
complete Git diff from `source_sha` to `H` is exactly one append to
`docs/tenkz/SOAK-1.0.md`: this freeze block. Candidate CI checks the
self-reference, append-only diff, source pull request, tag, immutable 0.9
payload, current prerequisite state, and entry grammar, then reports
`freeze-pending`. It cannot record the future merge SHA or time.

After merge, let `I = record_pr.mergeCommit.oid`. GitHub must report the PR
merged to `main`; the integration parent `P` from the common rule must equal
`source_sha`; `I` must be a strict descendant of `source_sha`; and the Git tree
of `I` must equal the Git tree of `H`. GitHub's verified `record_pr.mergedAt`
is the attempt-activation instant `T`, and `I` is its ancestry anchor.
Every derived prerequisite must be closed with `closedAt <= T`. A tree, source,
tag, prerequisite, or external-identity mismatch requires a `record-invalid`
reset targeting this freeze. A tagger timestamp may appear in `evidence`, but
it never determines ordering.

If `main` advances after `source_sha` but before this record integrates, no
attempt has started: abandon the unused tag and repeat the source/tag step with
a `PATCH` larger than the complete tag-namespace maximum. Reusing or moving the
stale tag is forbidden.

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
a missing or ambiguous merge base fails closed. `P` must be an ancestor of
`H`, hence `B = P`; for a two-parent integration, the second parent must equal
`H`. The work qualifies exactly when all of these predicates hold:

- GitHub reports `work_pr` merged to `main`, with non-null final
  `headRefOid`, `mergedAt`, and `mergeCommit.oid`.
- `I` is reachable from `main` and is a strict descendant of the active
  freeze record's integration commit, and the Git tree of `I` equals the Git
  tree of `H`.
- The complete path set changed from `B` to `H` contains neither
  `docs/tenkz/DESIGN.md` nor
  `docs/tenkz/SOAK-1.0.md`.
- The complete Git diff from `B` to `H` has a semantic addition or modification
  in the recorded class. At least one eligible path is a regular blob at `H`
  whose source-specific normalized token stream differs from its stream at `B`.
  A new file has an empty old stream. Comment-only, whitespace-only, empty-file,
  and deletion-only changes do not qualify. The `formalization-or-blueprint`
  class matches `TNLean/**/*.lean`, `blueprint/src/chapter/**/*.tex`, or
  `blueprint/src/appendix/**/*.tex`. The `rmp-benchmark` class matches
  `tests/tenkz/rmp/**/cases/*.tex`. `TNLean/Archive/**` is excluded from every
  work class.
- `work_pr` is not `armed_by_pr`, a `source_pr`, any entry's `record_pr` or
  `replay_receipt_pr`, or a `work_pr` already named by another entry.
- A repository-authorized reviewer distinct from the normalized
  `work_pr.author.login` has a latest effective `APPROVED` review on the exact
  final `headRefOid`, submitted before
  `work_pr.mergedAt`.

Glob matching is against slash-separated repository paths. `*` spans zero or
more non-slash characters within one component, while `**` spans zero or more
complete path components. The immutable `B`-to-`H` Git diff, not an
integration's final commit alone or a PR title, label, description, or entry
summary, decides path eligibility. The normalizer uses a deterministic
source-specific lexer: it removes Lean or TeX comments while respecting nested
Lean comments, escapes, and quoted literals, tokenizes the remaining source,
and ignores only inter-token whitespace. Literal and command content remains
semantic.

Class-specific checks run at `H`. Every changed eligible Lean module must build,
and its complete diff may introduce no proof-integrity blocker. When a blueprint
file supplies the qualifying change, `leanblueprint checkdecls`,
`leanblueprint web`, and `leanblueprint pdf` must pass from `blueprint/`. Every
changed or added RMP case supplying the
qualifying change must resolve through `tests/tenkz/rmp/manifest.toml`; for each
resolved target, `python3 scripts/tenkz_rmp.py check --id TARGET` must pass its
provenance, lint, audit, and compile stages. Missing tools, unresolved cases,
skipped stages, or incomplete execution fails closed.

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
(`fix-compatible`, `defer-to-2.0`, or `restart-required`), `summary` (`text`),
and `evidence` (`text`). A `fix-compatible` friction additionally requires
`regression_tests` (a nonempty `list[test-ref]`); that field is forbidden for
the other triages. `defer-to-2.0` changes nothing in the active major.
`restart-required` is mandatory when the frozen surface must break or no pinned
atomic assertion can witness the finding. It requires a reset as the next
non-correction entry.

Let `Q` be the active freeze's exact `freeze_tag`, `H_E` the friction record's
exact final head, and `I_E` its later integration. Every named inventory test's
`surface` must equal the friction's exact `surface`. Candidate validation
requires each `observe-release-test(H_E, Q, R)` receipt to return
`assertion-failed` with its exact pinned fingerprint; post-merge validation
requires the same at `I_E`. The friction must receive a later `resolution`
before the active attempt can proceed to release preparation or sign-off.

### `resolution`

Required additional fields: `friction` (`entry-ref`), `fix_pr` (`pr-ref`),
`summary` (`text`), and `evidence` (`text`). It can resolve only one preceding,
unresolved `fix-compatible` friction entry in the same active attempt. It cannot
resolve or reclassify another triage.

Let `H_F = fix_pr.headRefOid` and `I_F = fix_pr.mergeCommit.oid`. GitHub must
report `fix_pr` merged to `main` after the friction record, with non-null author,
`H_F`, `mergedAt`, and `I_F`. Let `P_F` be `I_F`'s sole parent for a one-parent
integration or first parent for a two-parent integration, and let `B_F` be the
unique merge base of `H_F` and `P_F`. A missing object, zero or more than two
parents, or missing or ambiguous merge base fails closed. `P_F` must be an
ancestor of `H_F`, hence `B_F = P_F`; for a two-parent integration, the second
parent must equal `H_F`. `I_F` is reachable from `main`, its tree equals
`H_F`'s tree, and it is a strict descendant of both the active freeze record
and the named friction record integrations. It is an ancestor of the resolution
record's candidate target `C` and, after merge, a strict ancestor of its
integration `I`.

A repository-authorized reviewer distinct from the normalized fix-PR author
must have a latest effective `APPROVED` review on the exact `H_F`, submitted before
`fix_pr.mergedAt`. The complete `B_F`-to-`H_F` diff may not touch
`docs/tenkz/DESIGN.md` or this ledger. For every regression test, at least one of
its declared program blobs must be modified, match the pinned policy's
`tex_api_fix_paths` for `surface = "tex-api"` or `tnlog_fix_paths` for
`surface = "tnlog"`, and change semantically. A TeX or style blob uses the TeX
normalizer defined for work entries. The canonical Python reader must parse
under the pinned interpreter and uses its location-free `ast.dump` as the
semantic stream. Every declared fixture blob, mode, and tree OID for the named
tests must be identical at `H_E`, `I_E`, `B_F`, `H_F`, and `I_F`; the
tag-derived manifest must also be byte-identical at those trees. A comment-only,
whitespace-only, empty-file, deletion-only, test-only, fixture-changing, policy-only,
title, label, description, or unrelated Lean change is not a fix.

Let `Q` be the active freeze's exact `freeze_tag`. For every test `R` named by
the friction, `observe-release-test(B_F, Q, R)` must return the same pinned
`assertion-failed` fingerprint observed at the friction, while
`observe-release-test(H_F, Q, R)` must return `passed`.
`validate-release-payload(H_F, Q)` must then pass, binding the complete pinned
inventory, tag-derived manifest, canonical artifacts, and receipts. Candidate
validation rechecks the fix PR, review, Git objects, complete diff, ancestry,
ordering, surface witness, before-and-after regression receipts, and full
tag-bound payload before reporting `resolution-pending`; post-merge validation
reruns all of them before the friction is resolved. Descriptive `summary` or
`evidence` text cannot replace any fix fact.

### `reset`

Required additional fields: `cause` (`restart-required` or `record-invalid`),
`target` (`entry-ref`), `reason` (`text`), and `evidence` (`text`). A
`record-invalid` reset additionally requires `replay_receipt_pr` (`pr-ref`) and
`replay_receipt_sha256` (`sha256`); those fields are forbidden on a
`restart-required` reset.

For `cause = "restart-required"`, `target` names an unresolved friction entry
with that triage in the active attempt; the reset uses and closes that attempt.
For `cause = "record-invalid"`, `target` names any earlier entry whose externally
verified identity, history, ancestry, tree, complete record diff, or ordering
evidence is invalid. If an attempt is active, the reset uses and closes it. If
none is active, it uses the most recently opened attempt and leaves the campaign
inactive. In either case it occupies its required position in the audit
batch's reset queue, not necessarily the position immediately following its
historical target, and a correction cannot repair the cause. Once this reset
passes its own current post-merge validation, it acknowledges the target only
when `cause = "record-invalid"`; this prevents the same defect from being queued
forever. A `restart-required` reset never acknowledges a raw-invalid entry.

The next freeze has attempt number one higher than the most recently opened
attempt, a strictly larger `PATCH`, a new source pull request and SHA, a new
annotated tag name and object, and a new record pull request. Its `source_sha`
must be a strict descendant of the latest reset's
`record_pr.mergeCommit.oid`.

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
| `release_prep_pr` | `pr-ref` |
| `release_tag` | `tag`, exactly `tenkz-v1.0.0` |
| `reviewer` | `identity` |
| `work_evidence` | `list[entry-ref]` |
| `decision` | the exact string `release` |

`freeze` and `source_sha` must match the active attempt. `work_evidence`
contains exactly the active attempt's two work-entry IDs: one
`formalization-or-blueprint` entry and one `rmp-benchmark` entry. Each work PR
fills only its recorded class, and the work-entry rules make the referenced
work PRs distinct. Values are entry references, not pull-request references.

Let `R` be the `release_prep_pr` named by the entry, with exact final head `H_R`,
integration `I_R`, and integration parent `P_R` defined as for a work PR. `R`
must be distinct from the activation PR and every source, work, entry-record,
and replay-receipt PR, and must satisfy all of these externally checked
predicates:

- GitHub reports `R` merged to `main` after both named work PRs, with non-null
  `headRefOid`, `mergedAt`, and `mergeCommit.oid`.
- `I_R` is reachable from `main`, is a strict descendant of both named work
  integrations, and has the same tree as `H_R`.
- `P_R` is an ancestor of `H_R`; the unique merge base equals `P_R`; and a
  two-parent integration's second parent equals `H_R`.
- Every `fix-compatible` friction in the active attempt has one validated
  resolution whose record integration is an ancestor of `P_R`, and no condition
  in that attempt requires a reset.
- The complete immutable `P_R`-to-`H_R` path set is exactly the 1.0 manifest
  path and the four canonical release-artifact paths from the pinned policy;
  all five blobs change.
- A repository-authorized reviewer distinct from `R`'s author has a latest
  effective `APPROVED` review on `H_R`, submitted before `R.mergedAt`.
- `validate-release-payload(H_R, tenkz-v1.0.0)` passes.

The sign-off's `record_pr` is the sign-off pull request. It changes only the
sign-off append under the common rule. Let `H` be its exact final `headRefOid`.
The current target tip `C` must equal `I_R`; `H` therefore descends from the
release preparation and both work integrations with `C` as its unique merge
base. `validate-release-payload(H, tenkz-v1.0.0)` must pass again. Candidate CI
validates those facts at `H` and reports `sign-off-pending`; it cannot invent
the future merge time or integration commit. That approved head therefore
carries the byte-identical externally bound release preparation and this
sign-off entry.

After merge, GitHub must report that `record_pr` targeted `main`. Let
`I = record_pr.mergeCommit.oid`; `I` must be a strict descendant of `I_R`, both
named work integrations, and the active freeze integration. The common
integration parent `P` must equal `I_R`, and the Git tree of `I` must equal the
Git tree of the approved `H`. Let `W` be the latest GitHub `mergedAt` among the
work PRs named by `work_evidence`. GitHub's
`record_pr.mergedAt` must be later than both `W` and `R.mergedAt`, and normalized
`mergedBy` must equal the pinned policy's `maintainer_identity`. The entry's
reviewer is repository-authorized and distinct from that maintainer and from
the normalized record-PR author. That reviewer's latest effective review must
be `APPROVED` on `H`, with
`submittedAt` later than both
`W` and `R.mergedAt` and earlier than `record_pr.mergedAt`. There is no further
waiting interval: sign-off can proceed as soon as the class coverage,
independent exact-head approvals, release preparation, and all other predicates
hold.

All `fix-compatible` friction in the active attempt must remain resolved, every
work predicate must still hold, and no condition may require a reset. Post-merge
validation also revalidates the pinned policy hash and ledger prefix and every
active-freeze fact: its record integration and start time, immutable annotated tag object and
peel to `source_sha`, source-PR integration, valid 0.9 payload at `source_sha`,
and the current closed state and `closedAt <= T` of every derived prerequisite.
A reopened or reclosed prerequisite, moved or replaced freeze tag, changed
source fact, invalid 0.9 payload, or pinned-byte mismatch requires a
`record-invalid` reset targeting the active freeze. A sign-off tree,
sign-off-specific external-fact, or
`validate-release-payload(I, tenkz-v1.0.0)` mismatch requires that reset
targeting the sign-off. Neither case is a validated sign-off. After post-merge
validation succeeds, the campaign is `signed-off-awaiting-tag` and the
annotated `tenkz-v1.0.0` tag may be created on `I`. The tag must not exist
before that success. Until the exact annotated tag object is observed peeling
to `I`, an absent final-tag ref leaves the campaign awaiting creation. All
mutable external facts remain subject to revalidation, and drift while the ref
is absent requires the ordered reset process above.

Every validation, including one whose snapshot already contains the final tag,
first replays the complete pinned policy, ledger, payload, Git, and GitHub
evidence through the validated sign-off. A tag lookup may not short-circuit
that replay. The current object named `tenkz-v1.0.0` must then be annotated and
peel to the validated sign-off integration `I` under the required current
no-update, no-delete, no-bypass protection. That observation changes the
campaign to terminal `released` state. No later ledger entry or new sign-off is
valid. Every later validation still replays every current mutable fact. A
mismatch that requires the ordered reset process while the final-tag ref is
absent becomes a hard release incident once that ref exists; it never reopens
the ledger. Creating the protected name with the wrong kind or target is also a
hard release incident. Weaker current protection, or a moved or replaced
present tag, is likewise a hard release incident. An absent final-tag ref always
remains `signed-off-awaiting-tag`: this state-based contract stores no immutable
prior-observation witness and does not claim to detect deletion by a trusted
administrator. No incident is repaired by deleting, moving, or reusing the
name, and none starts another 1.0 attempt.

No entry may be appended while `enforcement = "pending"`. The activation slice
under #5352 will add validation commands only after their scripts,
repository-evidence resolver, tests, CI wiring, closed inventory, blocker
chain, and tag protection are complete on `main`.

<!-- tenkz-soak-entries: append below only while enforcement=armed -->
