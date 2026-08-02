# tenkz compatibility and release policy

This file is the authority for compatibility, package versions, release tags,
and the 1.0 soak. `LANGUAGE.md` owns the public mental model,
`LANGUAGE-1.0.md` owns the frozen 1.0 grammar, and `ARCHITECTURE.md` owns the
implementation boundaries. The earlier file at `history/DESIGN.md` records the
0.6 design campaign; it does not define the released contract.

Adopting this policy neither changes the package version nor starts the 1.0
soak. Automated enforcement is pending under #5352, and no soak entry is valid
until the policy, repository-evidence checks, and CI wiring are armed. The
enforcement activation pins the ledger prefix but starts no clock. A later,
self-referential attempt-activation pull request supplies the trusted start
time after every prerequisite below has closed.

The following block is normative. A later #5352 slice activates its
machine-checking contract.

```toml tenkz-policy-v1
[policy]
schema = 1
enforcement = "pending"
enforcement_transition = "pending-to-armed"
tag_namespace = "tenkz-v*"
repository_tag_namespace = "v*"
freeze_tag_pattern = "tenkz-v0.9.PATCH"
freeze_tag_kind = "annotated"
soak_days = 28
event_format_implementation = "pending"
event_format_owners = ["#4162", "#4703"]
soak_blocker_chain = [["#5086", "#4699", "#4162"], ["#4703", "#4708", "#4163"]]
deprecation_removal = "not-before-next-major"
tombstone_reuse = false
frozen_twin_scope = "library-entry-point-in-same-package"
frozen_twin_lifetime = "permanent"
frozen_twin_precedent = "quantikz/quantikz2"
maintainer_identity = "github:lionsr"
signer_identity_scheme = "github:lowercase-login"

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

These classifications govern the 0.9 release candidate from its valid freeze
through the 1.0 soak, and every release beginning with 1.0. They do not freeze
the current v0.7 transitional surface. Before the freeze, the v0.7-to-v0.9
migration remains governed by `LANGUAGE-1.0.md`, the shrink ledger, and the
ordered prerequisite issues below.

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
namespace. `PATCH` is a non-negative decimal integer. A package tag is
annotated and points to a commit at which the `\ProvidesPackage` version and
date, manual version, change record, event-format declaration, and
compatibility tests all agree with the tag. A moved or reused release tag is
invalid.

The soak freeze tag matches `tenkz-v0.9.PATCH`. `PATCH` starts at any
non-negative decimal integer and increases strictly between attempts. For each
attempt, first merge the frozen source through a source pull request targeting
`main`, then create and push the annotated tag on that pull request's
integration commit. Only then open the ledger-only attempt-activation pull
request and append its self-referential `freeze` entry.

The entry records its own `activation_pr`, the prior `source_pr` and
`source_sha`, the tag name and object SHA, the prerequisites, and closure
evidence. It cannot record its own integration commit or merge time because
neither exists before merge. Candidate CI validates every fact already known
and reports `freeze-pending`. After merge, GitHub's verified `mergedAt` is the
clock anchor `T`; the pull request's external integration commit anchors later
ancestry. The validator checks the source pull request, source SHA, tag object,
and peeled commit agree, and rejects a lightweight, moved, replaced, or
mismatched tag. A tagger timestamp, if transcribed as evidence, is descriptive
only and never starts the clock.

The final `tenkz-v1.0.0` annotated tag is created only after the self-referential
sign-off pull request has landed on `main`. Its exact final head already carries
the 1.0 `\ProvidesPackage` metadata, manual version, change record, event-format
declaration, compatibility tests, and sign-off entry. The final tag points to
that pull request's integration commit. Sign-off records the intended release
tag but cannot require that tag to exist yet; requiring it earlier would make
the ledger and tag circular.

## The 1.0 freeze and soak

The dependency chain is ordered:

1. land the checker, repository-evidence resolver, tests, and CI; change both
   normative enforcement fields from `pending` to `armed` and pin the ledger
   prefix without starting a clock;
2. close #5086, #4699, and #4162 for 0.8;
3. close #4703, #4708, and #4163 for the 0.9 contract freeze;
4. merge the frozen source through a source pull request to `main`, then create
   and push an annotated `tenkz-v0.9.PATCH` tag on its integration commit;
5. open a ledger-only draft pull request, append a self-referential `freeze`
   entry, observe `freeze-pending` in candidate CI, and merge it to start the
   attempt at GitHub's verified merge time `T`;
6. expose that frozen documented contract to 28 elapsed days of normal
   blueprint work on `main`;
7. merge the independently approved sign-off pull request, then create
   `tenkz-v1.0.0` on its integration commit.

Every prerequisite must be closed, with GitHub `closedAt <= T`. Window `i` is
the half-open UTC interval `[T + 7i days, T + 7(i+1) days)` for
`i = 0, 1, 2, 3`; work merged exactly on a boundary belongs to the later
window, and `T + 28 days` lies outside the fourth window. Ordinary-work
evidence names at least one pull request in each window. GitHub must report it
merged to `main` in that interval. Its integration commit must be reachable
from `main` and a strict descendant of the attempt-activation pull request's
external integration commit. The work must perform normal blueprint or
benchmark work. Source, activation, policy-only, ledger-only, synthetic, and
unmerged work does not qualify.

Interface friction is appended when found and triaged as `fix-compatible`,
`defer-to-2.0`, or `breaking-required`. A reset has cause
`breaking-required` or `record-invalid` and names the entry that caused it. It
closes the attempt; the next non-correction entry starts attempt number one
higher with a strictly larger `PATCH`, a new source pull request and SHA, a new
annotated tag and object, and a new attempt-activation pull request. Compatible
fixes retain the clock only when both public surfaces remain compatible under
the rules above. Corrections remain owned by the attempt of their target even
after a reset and never reopen a closed attempt.

The sign-off entry names its own pull request. GitHub's `mergedAt` is the
sign-off time and must be at least `T + 28 days`; `mergedBy` must be
`github:lionsr`. The named, distinct reviewer must have a latest effective
`APPROVED` review on the exact final head, submitted after `T + 28 days`
and before merge. Sign-off also requires one qualifying work entry in each
window, no unresolved fix-compatible friction, and no breaking-required or
record-invalid condition in the active attempt. The exact entry grammar and
reset rules live in `SOAK-1.0.md`.
