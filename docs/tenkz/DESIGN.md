# tenkz compatibility and release policy

This file is the authority for compatibility, package versions, release tags,
and the 1.0 soak. `LANGUAGE.md` owns the public mental model,
`LANGUAGE-1.0.md` owns the frozen 1.0 grammar, and `ARCHITECTURE.md` owns the
implementation boundaries. The earlier file at `history/DESIGN.md` records the
0.6 design campaign; it does not define the released contract.

Adopting this policy neither changes the package version nor starts the 1.0
soak. The clock starts only with a valid freeze entry appended to
`SOAK-1.0.md` after every prerequisite below has closed.

The following block is normative and machine checked by
`scripts/check_tenkz_policy.py`.

```toml tenkz-policy-v1
[policy]
schema = 1
tag_namespace = "tenkz-v*"
repository_tag_namespace = "v*"
freeze_tag_pattern = "tenkz-v0.9.PATCH"
freeze_tag_kind = "annotated"
soak_days = 28
event_format_implementation = "pending"
event_format_owners = ["#4162", "#4703"]
soak_blocker_chain = [["#5086", "#4699", "#4162"], ["#4703", "#4708", "#4163"]]
deprecation_removal = "next-major"
tombstone_reuse = false
frozen_twin_scope = "library-or-package-entry-point"
frozen_twin_lifetime = "permanent"
frozen_twin_precedent = "quantikz/quantikz2"
maintainer_identity = "github:lionsr"
signer_identity_scheme = "github:lowercase-login"

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

Every `.tnlog` is a side contract for audit tools. Its event kinds, field
names, field meanings, required and forbidden fields, ordering rules,
escaping, and picture ownership are public. `scripts/tenkzlib/tnlog.py` owns
the canonical reader; event emitters own the writer; the golden-event ledger
guards byte stability but is not a substitute for a schema.

Before the 0.9 freeze, every stream must carry one explicit machine-readable
event-format version. The format has its own `major.minor` number. Writers emit
one declared version. Readers accept every supported minor revision of their
current event major and reject an unsupported major with a direct diagnostic.
The exact header spelling and its implementation remain owned by #4162 and
#4703. This policy does not implement or pre-empt that change.

Package and event versions move together when the event surface moves:

- a package patch leaves event bytes and meaning unchanged;
- an additive event change increments the event minor and requires at least a
  package minor;
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

A deprecation starts in a minor release. It names one replacement, the first
major release allowed to remove it, and tests proving that the old spelling
still has its promised behavior. A warning cannot become a compilation error
inside the same major series.

When removal occurs, the dead spelling becomes a tombstone. The linter and
parser reject it with its migration. Tombstones are permanent and their names
are never recycled, including at a later major release. Pre-1.0 aliases and
their milestone sunsets remain governed by `LANGUAGE-1.0.md` and the shrink
ledger; they must be resolved before the freeze.

The frozen-twin escape hatch is a permanent library- or package-entry-point
split. The owner-approved model is `quantikz` 0.9.8 frozen beside `quantikz2`
under a new library name in the same package. When a successor cannot preserve
the released surface, the old entry point remains installable with byte-tested
TeX and `.tnlog` behavior, while the new language ships beside it under a
distinct library or package entry point. The old surface receives no new
features and is never removed by the successor's next major release. The
release issue must cite the incompatibility, test both surfaces, and publish
both manuals and tag lines. A per-command alias, a spelling-level twin removed
at the next major, a compatibility switch, or a silent semantic change is not
the frozen-twin escape hatch. This policy defines the ownership decision; it
does not create the successor entry point.

## Release tags

Package tags use `tenkz-vMAJOR.MINOR.PATCH`. Repository tags named
`vMAJOR.MINOR.PATCH` belong to the Lean toolchain and are a distinct
namespace. A package tag is annotated and points to a commit whose
`\ProvidesPackage` version and date, manual, change record, event-format
declaration, and compatibility tests agree. A moved or reused release tag is
invalid.

The soak freeze tag is specifically `tenkz-v0.9.PATCH`. Create and push that
annotated tag on the frozen source commit before appending the first ledger
entry. The entry records the tag object's SHA, its peeled commit SHA, and the
tagger timestamp normalized to UTC; the validator checks all three and rejects
a lightweight, moved, replaced, future-dated, or backdated tag. The ledger
therefore lives in a later commit and does not ask a tag to contain the entry
that records it.

The final `tenkz-v1.0.0` annotated tag is created only after the sign-off entry
has landed on `main`. It points to the sign-off-containing commit. Sign-off
records the intended release tag but cannot require that tag to exist yet;
requiring it earlier would make the ledger and tag circular.

## The 1.0 freeze and soak

The dependency chain is ordered:

1. close #5086, #4699, and #4162 for 0.8;
2. close #4703, #4708, and #4163 for the 0.9 contract freeze;
3. create and push an annotated `tenkz-v0.9.PATCH` tag on the frozen source
   commit;
4. append its tag-object SHA, peeled commit SHA, tagger UTC timestamp, and
   closure evidence to `SOAK-1.0.md` in a later commit;
5. expose that exact frozen surface to 28 consecutive calendar days of normal
   blueprint work on `main`;
6. land sign-off, then create `tenkz-v1.0.0` on the sign-off-containing commit.

Ordinary-work evidence is recorded at least once in each seven-day window. An
entry records an immutable commit SHA reachable from `main`, its verified
committer timestamp in UTC, and the blueprint or benchmark work it performed.
Synthetic tests and unmerged branches do not qualify. Interface friction is
appended when it is found and triaged as `fix-compatible`, `defer-to-2.0`, or
`breaking-required`. A breaking need appends an immediate reset and ends that
attempt; a fresh freeze entry starts attempt number one higher. Compatible
fixes retain the clock only when both public surfaces remain compatible under
the rules above. A fresh attempt uses a new annotated tag name, tag object, and
peeled post-fix commit descending from the prior freeze; none may be reused.

Release sign-off is computed against current UTC and the verified Git objects,
not self-declared ledger dates. It requires the latest tagger timestamp to be
at least 28 days old, one reachable normal-work commit in each of the first
four weekly windows, no unresolved fix-compatible friction, no
breaking-required friction in the active attempt, and normalized explicit
identities for `github:lionsr` and one distinct independent reviewer. The
append-only entry grammar and reset rules live in `SOAK-1.0.md`.
