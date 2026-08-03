# tenkz compatibility and release policy

This file is the authority for compatibility, package versions, release tags,
and the 1.0 release-evidence campaign. `LANGUAGE.md` owns the public mental model,
`LANGUAGE-1.0.md` owns the frozen 1.0 grammar, and `ARCHITECTURE.md` owns the
implementation boundaries. The earlier file at `history/DESIGN.md` records the
0.6 design campaign; it does not define the released contract.

Adopting this policy neither changes the package version nor starts the 1.0
campaign. Automated enforcement is pending under #5352, and no campaign entry
is valid until the implementation and blocker chain below are complete. The
enforcement-activation pull request is the final prerequisite before a source
candidate. Its base contains the checker, repository-evidence resolver, tests,
CI wiring, closed release-test inventory, and active tag-protection ruleset. Its
complete diff is restricted to the seven activation scalars defined in
`SOAK-1.0.md`: the two enforcement values, inventory digest, test-code tree,
test-support tree, policy digest, and its own pull-request reference. This pins
the inventory, test implementation and acceptance data, enforcement workflow,
policy, and ledger prefix without allowing activation to replace any of them.
A later
self-referential freeze-entry pull request supplies the trusted attempt-ordering
anchor.

The following block is normative. A later #5352 slice activates its
machine-checking contract.

```toml tenkz-policy-v1
[policy]
schema = 1
enforcement = "pending"
enforcement_transition = "pending-to-armed"
tag_namespace = "tenkz-v*"
repository_tag_namespace = "v*"
tag_immutability = "github-ruleset-no-update-delete-or-bypass"
freeze_tag_pattern = "tenkz-v0.9.PATCH"
freeze_tag_kind = "annotated"
required_distinct_work_prs = 2
work_classes = ["formalization-or-blueprint", "rmp-benchmark"]
one_class_per_work_pr = true
work_excluded_paths = ["TNLean/Archive/**"]
tex_api_fix_paths = ["tex/tenkz/*.tex", "tex/tenkz/*.sty"]
tnlog_fix_paths = ["tex/tenkz/*.tex", "tex/tenkz/*.sty", "scripts/tenkzlib/tnlog.py"]
event_format_owners = ["#4162", "#4703"]
soak_blocker_chain = [["#5086", "#4699", "#4162"], ["#4703", "#4708", "#4163"]]
deprecation_removal = "not-before-next-major"
tombstone_reuse = false
frozen_twin_scope = "library-entry-point-in-same-package"
frozen_twin_lifetime = "permanent"
frozen_twin_precedent = "quantikz/quantikz2"
maintainer_identity = "github:lionsr"
github_identity_scheme = "github:lowercase-login"
reviewer_repository_permissions = ["write", "admin"]
release_manifest_pattern = "docs/tenkz/releases/TAG.toml"
release_package_metadata = "tex/tenkz/tenkz.sty"
release_manual = "docs/tenkz/manual2.tex"
release_change_record = "docs/tenkz/CHANGES.md"
release_event_format = "docs/tenkz/TNLOG.md"
release_test_inventory = "tests/tenkz/release-tests.toml"
release_test_inventory_sha256 = "pending"
release_test_code_root = "tests/tenkz/release-harness"
release_test_code_tree = "pending"
release_test_support_root = "tests/tenkz/release-support"
release_test_support_tree = "pending"
release_test_subject_roots = [
  "tex/tenkz",
  "scripts/tenkzlib/tnlog.py",
  "docs/tenkz",
  "tests/tenkz/rmp",
]
release_enforcement_workflows = [".github/workflows/tenkz-release-policy.yml"]
release_workflow_dependencies = "transitive-content-addressed-no-runtime-downloads"
release_enforcement_network = "disabled-before-repository-code"
release_reset_replay_schema = "tests/tenkz/release-support/reset-replay-v1.schema.json"
release_tag_signature = "ssh-ed25519"
release_tag_public_key = "tests/tenkz/release-support/final-tag-signing-key.pub"
release_tag_object_schema = "tests/tenkz/release-support/final-tag-object-v1.schema.json"
release_publisher_environment = "tenkz-release-publisher"
release_publisher_secret = "TENKZ_FINAL_TAG_SIGNING_KEY"
release_publisher_secret_scope = "environment-only-no-shadow"
release_publisher_key_retirement = "required-before-released"
release_publisher_workflow_root = ".github/workflows"
release_test_dependency_contract = "pinned-harness-support-declared-subject-roles"
release_test_protocol = "hermetic-repository-view-no-shell-or-network"

[event_format]
reader_accepts = "same-major-any-minor"
unknown_optional_fields = "ignore"
unknown_event_kinds = "explicitly-ignorable-only"
non_ignorable_change = "major"

[compatibility.patch]
tex_api = "backward-compatible-fix"
tnlog = "byte-stable"

[compatibility.minor]
tex_api = "backward-compatible-addition"
tnlog = "additive-versioned"

[compatibility.major]
tex_api = "breaking-change"
tnlog = "breaking-versioned"
```

## Compatibility ownership

tenkz has two public surfaces. A release decision names both; compatibility on
one cannot excuse a break in the other.

During an active attempt, `tex_api_fix_paths` constrains a compatible TeX-surface
fix and `tnlog_fix_paths` constrains a compatible event-surface fix. The former
admits only root package implementation files, never examples or fixtures. The
latter admits those event emitters and the canonical Python reader. Dedicated
pinned harness code supplies the evidence but is not a mutable fix surface.

These classifications begin at the valid 0.9 freeze. They do not preserve the
current v0.7 transition surface. Before the freeze, prefer the clean 1.0 model:
rename or remove an obsolete command, key, or event and update its callers in
the same change instead of adding a compatibility shim. `LANGUAGE-1.0.md`, the
shrink ledger, and the ordered prerequisite issues below govern that migration.

### TeX surface

The TeX surface consists of the documented environments, commands, keys,
closed value alphabets, defaults, diagnostics, and their mathematical and
rendered meaning. At the 0.9 freeze, `manual2.tex` and `chapters2/` become the
reader-facing contract. The executable registry at
`tex/tenkz/tenkz-language-registry.tex` is the machine inventory and must agree
with that manual. `LANGUAGE-1.0.md` governs the freeze migration until the
manual takes effect.

Private control sequences, stage-local records, and undocumented development
probes are not public. Exact raster bytes are not promised across engines or
font revisions. The topology, boundary meaning, labels, default semantic ink,
and successful compilation of documented valid input are promised.

### Event surface

At the 0.9 freeze, every `.tnlog` becomes a side contract for audit tools. Its
event kinds, field names, field meanings, required and forbidden fields,
ordering rules, escaping, and picture ownership are public.
`scripts/tenkzlib/tnlog.py` owns the canonical reader; event emitters own the
writer; the golden-event ledger guards byte stability but is not a substitute
for a schema.

Before the 0.9 freeze, every stream must carry one explicit machine-readable
event-format version. The format has its own `major.minor` number. Writers emit
one declared version. A reader accepts every minor revision of its event major
and rejects a different major with a direct diagnostic. It ignores unknown
optional fields. It ignores an unknown event kind only when the event schema
marks that kind explicitly ignorable and skipping it preserves the validity
and meaning of every recognized record. Any addition that cannot meet those
conditions increments the event major. The exact header and ignorable-kind
spellings and their implementation remain owned by #4162 and #4703. This
policy does not implement or pre-empt that change.

Package and event versions move together when the event surface moves:

- a package patch leaves event bytes and meaning unchanged;
- an additive event change increments the event minor and requires at least a
  package minor; readers of the same event major continue to accept it;
- a removed field, renamed kind, changed meaning, incompatible ordering, or
  incompatible escaping increments the event major and requires a package
  major;
- a package minor that changes only the TeX surface may leave the event version
  unchanged.

## Package versions

tenkz uses semantic `MAJOR.MINOR.PATCH` versions.

### Patch

A patch fixes a defect without rejecting documented valid input, changing a
documented default, or changing mathematical meaning. Clearance, clipping,
typography, and other rendering corrections are patches when topology,
boundary meaning, labels, and semantic ink stay fixed. A patch emits the same
`.tnlog` bytes and semantics for unchanged input. Parser-only diagnostic fixes
may be patches when they neither accept an invalid event as valid nor reject a
valid event.

### Minor

A minor release adds a backward-compatible documented capability. Existing
valid sources keep their meaning and defaults. New language elements still
pass the extension and shrink gates; a minor number is not permission for an
unmanifested special case. Deprecation may begin in a minor release, but the
old spelling continues to compile for the rest of the major series.

An additive `.tnlog` kind or optional field is a minor change only after the
event minor is incremented, the canonical reader accepts old and new minors,
and consumers are tested against both.

### Major

A major release may remove deprecated input, change a documented default or
meaning, or make an incompatible event-format change. The migration guide,
tombstones, manual, registry, parser, emitters, and tests change together. A
major release never reuses a dead spelling for a new meaning.

## Deprecations, tombstones, and frozen twins

A deprecation starts in a minor release. It names one replacement, the earliest
major release allowed to remove it, and tests proving that the old spelling
still has its promised behavior. Removal at that major is permitted, not
mandatory. A warning cannot become a compilation error inside the same major
series.

When removal occurs, the dead spelling becomes a tombstone. The linter and
parser reject it with its migration. Tombstones are permanent and their names
are never recycled, including at a later major release. Pre-1.0 aliases and
their milestone sunsets remain governed by `LANGUAGE-1.0.md` and the shrink
ledger; they must be resolved before the freeze.

The frozen-twin escape hatch is a permanent library-entry-point split inside
one package. The owner-approved model is `quantikz` 0.9.8 frozen beside
`quantikz2` under a new library name in the same package. When a successor
cannot preserve the released surface, the old library entry point remains
installable with byte-tested TeX and `.tnlog` behavior, while the new language
ships beside it under a distinct library entry point in that package. The old
surface receives no new features and is never removed by the successor's next
major release. The release issue must cite the incompatibility, test both
surfaces, and publish separate manuals and release-tag histories. A separate
package, a per-command alias, a spelling-level twin removed at the next major,
a compatibility switch, or a silent semantic change is not the frozen-twin
escape hatch. This policy defines the ownership decision; it does not create
the successor entry point.

## Release tags

Package tags use `tenkz-vMAJOR.MINOR.PATCH`. Repository tags named
`vMAJOR.MINOR.PATCH` belong to the Lean toolchain and are a distinct
namespace. `PATCH` is `0` or a nonzero decimal digit followed by decimal
digits; leading zeroes are forbidden. A package tag is
annotated and points to a commit at which the `\ProvidesPackage` version and
date, manual version, change record, event-format declaration, and
compatibility tests all agree with the tag. A moved or reused release tag is
invalid.

Every package tag has the manifest obtained by substituting its exact tag name
for `TAG` in the policy pattern. The policy, not the manifest, owns the four
canonical release-artifact paths, hashed test inventory, and pinned Git trees of
in-repository test code and immutable test support. The manifest repeats the
inventory digest and both tree OIDs so that payload validation binds them at the
exact candidate tree. Release artifacts, declared benchmark inputs, and the
canonical event reader remain mutable subjects. The dedicated pinned harness
separates their declared program files from non-executable fixtures; neither role
can provide harness helpers, coverage selection, expected results, allowlists,
or thresholds. The freeze validates
the 0.9 manifest, artifacts, and tests before its tag is created. The final
release-preparation pull request changes exactly the 1.0
manifest and four canonical artifacts. The tests run through the single pinned
protocol at the exact release head. This binds each payload to its tag and the
1.0 preparation to the reviewed pull request.

The inventory and test-tree pins in this policy belong only to the 0.9-to-1.0
campaign. They validate an active 0.9 freeze or `tenkz-v1.0.0`, not every future
package tag. After 1.0, a later release may adopt a new versioned policy,
inventory, and harness without editing or reopening this terminal ledger. The
public compatibility classifications survive; these particular evidence bytes
do not become permanent development constraints.

The closed enforcement-workflow list names regular Git blobs. Their exact blob
OIDs and modes at the activation integration are pinned through the immutable
`armed_by_pr` identity; they are not additional activation scalars. Every
candidate and post-merge validation resolves that integration and requires the
same blobs and modes at its exact validation target. A candidate diff touching
one of these paths is invalid. A GitHub check result counts only when its exact
head and executed workflow resolve to those pinned bytes. The independent
evidence-supervisor result is still required; a workflow status cannot replace
it. A missing, renamed, non-blob, or changed workflow fails closed.

Key isolation has a wider boundary than the one release workflow. Activation
also pins the complete Git tree at `release_publisher_workflow_root`. Until a
validation declares `released`, the current tree must equal that pin and the
dedicated environment must retain its protected-branch rule. Across that tree,
the publisher is the only job that may name the environment or private-key
secret; `secrets: inherit` is forbidden. The configured secret name exists only
in that environment. The same name in another environment in this repository,
at repository scope, or at organization scope with access to this repository
fails closed.

After a successful publisher job, an administrator removes the environment
secret. The validation that declares `released` requires its absence, and every
later replay rejects its reintroduction. Released replay checks the successful
job against the historical workflow tree at the sign-off integration, which
must equal the activation pin. It does not require unrelated current workflows
to remain frozen after the key is gone. Environment administrators remain
inside the explicit GitHub-administration trust boundary.

The resolver also closes the dedicated workflow's executable dependency graph.
A local action or reusable workflow is pinned by its activation Git object and
included in later byte-and-mode checks. Every external action or reusable
workflow uses a full commit SHA, never a tag or branch; every container uses a
content digest. Composite-action, called-workflow, interpreter, helper, package,
and runtime-fetched executable dependencies are checked recursively. A package
manager, downloader, unhashed lock, mutable resolution, unavailable object,
incomplete closure, or cycle fails closed. After GitHub materializes the
checkout and content-addressed dependencies, network access is removed before
repository code or a validation command runs. GitHub's control plane and hosted
runner remain inside the stated trust boundary; downloaded mutable executable
content does not.

The sole networked release step is the dedicated workflow's terminal publisher
job. It has no checkout and runs no repository code. GitHub starts it only after
the exact sign-off integration's network-disabled post-merge validator succeeds.

The publisher reads the final ref before deciding whether it needs the private
key. The pinned support tree supplies the SSH-Ed25519 public key and byte-level
object schema; only the absent-ref path receives the private key. The schema
fixes the tagger identity and timezone to `+0000`. The validator converts the
sign-off pull request's exact UTC `mergedAt` to one integer Unix second and
passes that `tagger_epoch_seconds` value; a fractional, non-UTC, ambiguous, or
out-of-range value fails closed. The schema specifies the complete Git
tag-object byte layout, the `git` SSH-signature namespace and embedding, and the
repository object-format hash. Its signed message binds the final name,
sign-off integration, policy hash, and ledger prefix.

The successful validator passes one closed tuple to its dependent job: `I`,
`tagger_epoch_seconds`, policy and prefix hashes, prefix boundary, and the
pinned support-tree, schema-blob, and public-key-blob OIDs. The publisher accepts
no caller-supplied replacement. It fetches those exact Git objects by OID
through the GitHub control plane and verifies their identities and hashes before
constructing `E`; it never reads a moving branch path.

After validation, the publisher first reads the final ref. If it is absent, the
publisher constructs `E`, verifies its raw signature against the pinned public
key, checks every schema byte and its peel, computes its object ID before any
write, and creates the already-verified object and ref without force. If an
uncertain earlier write already left the ref at `E`, a retry authenticates the
stored raw object and adopts it without reading the private key. Any other
present object is an incident. The job exits successfully only after a final
readback authenticates `E`; it emits no durable output receipt. Without the
private key, another actor cannot forge an acceptable object; replaying the
already-authorized `E` cannot change its name or target.

The evidence-campaign freeze tag matches `tenkz-v0.9.PATCH`. `PATCH` has the
canonical grammar `0|[1-9][0-9]*`. When a new freeze is proposed, its patch must
be strictly larger than every other patch in the complete current
`tenkz-v0.9.*` tag namespace and every earlier freeze entry. Thus an abandoned
tag that never obtained a ledger entry still raises the next candidate's floor.
The freeze entry retains the complete numerically sorted tag-name snapshot seen
by that exact successful candidate check. A tag absent from the retained
snapshot is a later reservation and does not retroactively invalidate the
earlier freeze; historical replay requires the current namespace to contain the
entire retained snapshot, checks the freeze's exact protected object, and checks
its stable ordering above earlier freeze entries. For each attempt, first merge
the frozen source through a source pull request targeting `main`. A
repository-authorized reviewer distinct from its author approves its
exact final head before merge, and its integration tree equals that approved
tree. The tree must carry
the tag-derived 0.9 manifest, canonical release artifacts, pinned test
inventory, and passing inventory commands. Then create and push the annotated
tag on GitHub's `source_pr.mergeCommit.oid`. Only then open the ledger-entry pull
request and append its self-referential `freeze` entry. The target branch must
remain at that source integration until the freeze record merges; an
intervening `main` commit invalidates the candidate before any attempt starts
and requires a new source/tag step with a larger unused `PATCH`.

Every entry records the pull request that first appends it as `record_pr`;
GitHub supplies that pull request's author, final head, merge time, and
`mergeCommit.oid`. A freeze also records the prior `source_pr` and
`source_sha`, the tag name and object SHA, the prerequisite chain flattened in
row-major order from the pinned policy, and descriptive evidence. It cannot
record its own integration commit or merge time because neither exists before
merge. Candidate CI validates every fact already known and reports
`freeze-pending`. Candidate validation requires the current `main` tip to equal
`source_sha`; the source-to-head diff must be exactly one append to
`SOAK-1.0.md`. After merge, the integration's first parent must still equal
`source_sha`, and the integration tree must equal the approved final head's
tree. GitHub's verified `record_pr.mergedAt` is the attempt-activation instant
`T`, and `record_pr.mergeCommit.oid` anchors later ancestry. The validator
checks the source pull request, source SHA, tag object, and peeled commit agree,
and rejects a lightweight, moved, replaced, or mismatched tag. A tagger
timestamp, if transcribed as evidence, is descriptive only and never determines
ordering.

The same record provenance applies to every later entry. Candidate validation
must run on the declared `record_pr` at its exact final head, whose complete
pull-request diff is exactly one ledger-entry append and changes no other
path. Post-merge validation requires that pull request to be merged to `main`,
with its integration commit reachable from `main` and its tree equal to the
approved head. Copying an entry through another pull request, or mixing an
entry with implementation or release-preparation changes, is invalid and
requires a `record-invalid` reset after merge.

The final `tenkz-v1.0.0` annotated tag is created only after the self-referential
sign-off record has landed on `main` and passed post-merge validation. A
separate release-preparation pull request first lands the 1.0
`\ProvidesPackage` metadata, manual version, change record, event-format
declaration, and compatibility tests. The sign-off entry names that PR;
GitHub/Git evidence binds its exact approved head, complete diff, integration
tree, merge time, and ancestry after both work integrations. The sign-off record
pull request then changes only its ledger append, so its exact approved final
head carries that prepared state and the sign-off entry without mixing evidence
and implementation. Its exact validation target and final integration parent must
equal the release-preparation integration; an intervening `main` commit requires
another reviewed preparation on the new tip before any final tag exists.
GitHub supplies the record pull request's integration commit, whose Git tree
must equal that approved head's tree. The final tag points to that integration
commit. Sign-off records the intended release tag but cannot require that tag
to exist yet; requiring it earlier would make the ledger and tag circular. A
tree or ancestry mismatch requires a `record-invalid` reset and forbids the tag.

## The 1.0 freeze and evidence gate

The dependency chain is ordered:

1. land the checker, repository-evidence resolver, tests, CI, and closed test
   inventory;
2. close #5086, #4699, and #4162 for 0.8;
3. close #4703, #4708, and #4163 for the 0.9 contract freeze;
4. configure and verify the tag-protection ruleset, then use one
   self-referential enforcement-activation pull request to perform only the
   seven permitted scalar replacements and pin the inventory, test-code tree,
   test-support tree, exact armed policy hash, and ledger prefix;
5. merge the frozen source through an independently exact-head-approved source
   pull request to `main`, then create and push an annotated
   `tenkz-v0.9.PATCH` tag on its integration commit;
6. open a ledger-entry draft pull request, append a self-referential `freeze`
   entry, observe `freeze-pending` in candidate CI, and merge it to start the
   attempt at GitHub's verified merge time `T`;
7. merge two distinct qualifying real-work pull requests after `T`: one in the
   `formalization-or-blueprint` class and one in the `rmp-benchmark` class;
8. resolve every `fix-compatible` friction in the active attempt, then merge an
   independently exact-head-approved release-preparation pull request descending
   from both work integrations and all resolution records;
9. merge the independently approved sign-off record; its pinned post-merge
   workflow validates it, records the exact tag object, and then creates
   `tenkz-v1.0.0` on its integration.

Closing #5086 in step 2 means that its plane-basis capability has landed for
0.8. The `expiry 1.0` values on related SHRINK entries bound the later removal
of downstream migration flags; they do not move #5086 to the 1.0 milestone.

Every prerequisite must be closed, with GitHub `closedAt <= T`. Each qualifying
work pull request must be merged to `main` strictly after `T`. Its integration
commit must be reachable from `main` and a strict descendant of the freeze
record's external integration commit, and its tree must equal the independently
approved final head's tree. `SOAK-1.0.md` defines the immutable complete
merge-base-to-head diff, the two eligible-path predicates, the exclusion of
`TNLean/Archive/**`, and the one-class assignment rule. The two classes must be
filled by distinct pull requests; a pull request can fill only its recorded
class. The enforcement-activation PR, source PRs, entry record PRs, replay
receipt PRs, repeated work PRs, unmerged PRs, and any diff touching either
policy document do not qualify. A policy-, checker-, CI-, receipt-, or
record-only diff has no eligible class change and therefore does not qualify.

Interface friction is appended when found and triaged as `fix-compatible`,
`defer-to-2.0`, or `restart-required`. Use `restart-required` when the frozen
surface must break or no pinned atomic assertion can witness the finding. A
compatible resolution names the exact later fix pull request and a nonempty
list of the friction entry's immutable
pinned atomic regression tests. Each test reports its pinned assertion-failure
fingerprint at the recorded friction tree and immediately before the fix, while
its immutable fixtures remain byte-identical and its surface-owned program path
and assertion pass at the fix head under the active freeze tag. The fix pull
request's repository-authorized exact-head approval, integration tree, ancestry,
surface-specific semantic diff, and complete pinned test run are revalidated
before the friction is resolved. A reset has cause `restart-required` or
`record-invalid` and names the entry that caused it. A restart reset closes the
active attempt. A record-invalid reset targets any earlier externally invalid
entry; it closes the active attempt when one exists
and otherwise leaves the campaign inactive. A currently valid record-invalid
reset acknowledges its target while that reset remains valid; an audit queues
only invalid entries not already acknowledged by such a later reset. If the
acknowledging reset itself becomes invalid, its target is uncovered and both
defects require valid acknowledgements. Exact-head replay evidence proves each
historical reset's placement against its pre-reset prefix; the current audit
still uses the actual final-prefix boundary and only queues prospective drift.
That replay is durable: a separate, independently exact-head-approved receipt
pull request lands one new canonical receipt blob under
`docs/tenkz/soak-replay/` immediately before the ledger-only reset record. Its
closed schema comes from the pinned support tree. The reset entry binds the
receipt pull request and raw-blob digest. The reset integration and every later
validation tree retain that exact regular blob at its canonical path. Later
replay reads the retained blob from the exact current validation tree, not from
an old integration that history rewriting may make unreachable, an expiring
workflow artifact, or a newly supplied snapshot. The trusted approval,
maintainer merge, initial tree binding, carried-forward digest, and embedded
supervisor receipts establish its provenance. A missing retained blob can be
repaired only by restoring those exact bytes at the same path.
When an audit's reset queue is nonempty, its head is the first new
non-correction entry after the boundary. A pending `restart-required` reset
heads the queue; otherwise the earliest
unacknowledged invalid target's record-invalid reset does. Remaining targets
follow in ledger order, consecutively apart from corrections. External drift
may occur after
later historical entries already landed, so a reset need not be adjacent to its
target. Ignoring historical corrections and administrative resets, the next
freeze is attempt number one higher than the most recently opened attempt,
with a strictly larger `PATCH`, a new source pull request and SHA, a new
annotated tag and object, and a new freeze record.
Compatible fixes retain the active attempt only when both public surfaces remain
compatible under the rules above. A correction may target any historical
entry, remains owned by its target's attempt, and never changes attempt state.

The sign-off entry's `record_pr` is its own pull request. GitHub's `mergedAt`
is the sign-off time and must be later than both qualifying work merges;
normalized `mergedBy` must equal the pinned policy's `maintainer_identity`. The
named, distinct, repository-authorized reviewer's latest effective review must
be `APPROVED` on the exact final head, submitted
after the later qualifying work merge and the named release-preparation merge,
and before sign-off merge. The sign-off head and integration must descend from
all three integrations. The sign-off may proceed immediately once those ordered
facts hold. It also requires one qualifying work entry in each class, no
unresolved `fix-compatible` friction in the active attempt, and no condition
requiring reset. A validated sign-off first enters
`signed-off-awaiting-tag`; mutable evidence remains live until a full replay
succeeds. If the exact signed object appears but no publisher job has completed
successfully, the intermediate state is
`signed-off-awaiting-publisher-success`; a retry authenticates it. Once the job
succeeds, the campaign is `signed-off-awaiting-key-retirement` until the
environment key is removed. A later validation, not the publisher job, declares
terminal `released` state after observing the exact object, the successful
historical job, and the retired key; no entry follows it. There is no publisher
output receipt or compatibility state alias.

Every later validation still replays all current mutable facts. Before the
final tag exists, drift follows the ordered reset process; after the tag exists,
the same drift is a hard release incident and never reopens the ledger. Ruleset
administrators and the GitHub control plane are trusted: the validator does not
claim to detect drift or a protection gap that an administrator restores before
its snapshot. A wrong, moved, or replaced present tag is never repaired by
moving or reusing the name. An absent final-tag ref remains
`signed-off-awaiting-tag` unless a successful publisher job previously read it
back; later absence in that case is an incident. The exact entry grammar, state
transitions, external-fact rules, and reset rules live in `SOAK-1.0.md`.
