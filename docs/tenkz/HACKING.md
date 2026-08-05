# Hacking on tenkz

`LANGUAGE.md` is the public semantic contract.  `ARCHITECTURE.md` owns the
internal pipeline.  This file is the operational checklist for changing and
debugging the package.

## Fast build loop

Compile a standalone example from its own directory.  Keep the timeout: an
expl3 loop over an expanded `\q_no_value` otherwise looks like a slow run.

```sh
timeout 120 env TEXINPUTS="<repo>/tex/tenkz//:" \
  xelatex -interaction=nonstopmode -halt-on-error <file>.tex
```

Build the compact manual twice for contents and references:

```sh
python3 scripts/tenkz_manual_doctest.py
cd docs/tenkz
timeout 150 env TEXINPUTS="../../tex/tenkz//:" \
  xelatex -interaction=nonstopmode -halt-on-error manual2.tex
timeout 150 env TEXINPUTS="../../tex/tenkz//:" \
  xelatex -interaction=nonstopmode -halt-on-error manual2.tex
```

The generated language reference is
`chapters2/generated-language-reference.tex`.  Regenerate it from the
executable registry at `tex/tenkz/tenkz-language-registry.tex`; parser-facing
language code lives in `tex/tenkz/tenkz-language.code.tex`.  Do not edit the
generated file as an independent vocabulary list.  The manual has a short
fallback so a clean pre-generation checkout still compiles.

The RMP book has a separate driver and interface:

```sh
python3 scripts/tenkz_rmp.py check --id <target>
python3 scripts/tenkz_rmp.py check --section <section>
python3 scripts/tenkz_rmp.py check --all
python3 scripts/tenkz_rmp.py book --all
python3 scripts/tenkz_rmp.py render --all
python3 scripts/tenkz_rmp.py compare --all \
  --source-root References/RMP_TIKZ_SOURCE_CODE
```

Every command first runs the corpus-wide physical-dimension ownership check,
even when `check --id` selects one target.  Case dimensions are classified as
metric, projection/frame, route/string, or composition/layout and ratcheted in
`scripts/tenkzlib/dimensions.py`; comment dimensions fail separately.  The two
fixed benchmark-book page-layout files have exact path-specific counts and do
not count as figure geometry.  These core ceilings are aggregate ratchets:
net reductions pass and uncompensated count increases fail.  Exact balanced
replacements and ownership-site moves are rejected by the exact per-occurrence
inventory described below.

The comparison command requires a separate author-source tree supplied through
`--source-root`.  The canonical local home is the gitignored
`References/RMP_TIKZ_SOURCE_CODE/` directory.  It contains the authors'
standalone `ImagesReview Section II` through `ImagesReview Section V` source
drop used to establish the `author_source` and `author_lines` pairings in
`tests/tenkz/rmp/manifest.toml`; the source drop is not redistributed by this
repository.

The four cited section files are identified by
`tests/tenkz/rmp/author-source.sha256`.  `compare` verifies and snapshots those
files before compiling any corpus target, so a missing, edited, or different
source drop fails quickly and later filesystem changes cannot alter the
comparison.  Pairing verdicts are also bound to the source identities and
extraction ranges by `pairing_sha256` in `tests/tenkz/rmp/verdicts.toml`.
Generated PDFs, auxiliary files, logs, and filesystem metadata are not
provenance: only the section sources cited by the pairing manifest define the
external authority.  A source tree in another local directory is acceptable
only when it matches the committed hashes.

Per-target verdicts are stored in `tests/tenkz/rmp/verdicts.toml`, one
stanza per target.  Any status may be recorded, including failure; the check
rejects lies, never gaps: a stale `case_sha256`, a `faithful` claim without a
second viewer and a verified pairing, or a `blocked` entry that names no
missing capability all fail, while recorded gaps merely appear in the book's
histogram.  A judged verdict pins the SHA-256 of its case; editing the case
stales exactly that verdict.

The ordinary 257-fixture corpus keeps its existing default interface:

```sh
scripts/tenkz_corpus.sh
scripts/tenkz_corpus.sh --render
```

Both suites may share lower-level helpers; neither frontend changes the
other's defaults.

## Golden event streams

The event ledger is `tests/tenkz/golden-events.sha256`.

```sh
scripts/tenkz_golden.sh --check
```

The check recompiles every top-level `tests/tenkz/*.tex` standalone fixture and
requires each `.tnlog` event stream to be byte-identical to the stored SHA-256
baseline.  Nested suites such as `tests/tenkz/kernel/` have their own gates.
Run the command without an argument to take a new snapshot:

```sh
scripts/tenkz_golden.sh
```

Re-pin only when fixture source changes or a reviewed package contract change
intentionally changes the emitted events, and the new streams have been
reviewed as the intended contract.  Behavior-preserving package changes must
pass `--check`; they do not authorize a new baseline.

## Same-session pixel pairs

Pixel evidence compares two package revisions in one session:

```sh
scripts/tenkz_pixelpair.sh origin/main
```

The command creates a detached worktree at the base revision, renders the
renderer-only source manifest against that true legacy package and the current
package, rasterizes both at 300 dpi, and compares the paired pages byte for
byte.  A copied package tree is not a legacy control.  Stored raster hashes are
not cross-revision redraw evidence because raster bytes depend on the machine
and TeX epoch.  The exact-toolchain pins in
`tests/tenkz/kernel/golden-pixels.sha256` are a narrower regression gate:
after an approved XeTeX, Poppler, font, or intentional render change, inspect
the full-resolution fixtures.  Before re-pinning, run
`scripts/tenkz_kernel_probes.sh --check`: an expected pixel mismatch is
acceptable, but every non-pixel probe must pass, including structural
assertions, sugar-expansion parity, and the event-stream comparison.  If a
separate reviewed contract change intentionally affects a non-pixel pin, review
and update that contract first, then rerun until every non-pixel probe passes.
Do not snapshot after any non-pixel failure.  Then re-pin with
`scripts/tenkz_kernel_probes.sh --snapshot`, which updates both the pixel and
event ledgers.

This command exists for the redraw campaign and expires at its close, no later
than 1.0.  Do not turn it into a permanent raster manifest.

## Shrink sessions

The shrink checker reports six meters:

1. public vocabulary census;
2. parser-leaf paths;
3. escape-spelling use in the demand corpus;
4. mean non-comment lines across the 130 RMP cases;
5. aliases and their sunsets;
6. overloaded names, union types, and shared enum words.

```sh
python3 scripts/tenkz_shrink.py meters
python3 scripts/tenkz_shrink.py flags
python3 scripts/tenkz_shrink.py gate --base-ref origin/main
```

When any intentional change alters a computed meter—including a registry,
demand-corpus, or parser-source identity change—compute and review the new
baseline before the gate:

```sh
python3 scripts/tenkz_shrink.py meters > /tmp/tenkz-census-baseline.json
diff -u tests/tenkz/census-baseline.json /tmp/tenkz-census-baseline.json
cp /tmp/tenkz-census-baseline.json tests/tenkz/census-baseline.json
python3 scripts/tenkz_shrink.py gate --base-ref origin/main
```

At the start of a new 0.9 or 1.0 shrink session, advance
`CURRENT_MILESTONE` in `scripts/tenkz_shrink.py` in the same change.  The
`flags` and `gate` actions use that constant to decide which alias sunsets are
due.

The registry's implementation ledgers are `kernel` and `sugar(...)`: kernel
rows are one-in-one-out vocabulary, while sugar rows must expand into kernel
spellings and earn continued use.  The other status words record lifecycle
debt: `alias(...; sunset=...)` reads old sources until its stated rewrite, and
`escape` names raw geometry whose uses count in meter M3.

The gate first compares the pinned meters with the base revision.  M1 total or
kernel growth requires an `Extension-gate: #NNNN` citation, or a
`Census-correction: #NNNN` citation while parser identities are unchanged;
command or environment growth permits only the extension citation.  M2
path-count growth and every parser-leaf identity change, including replacement
or removal, require the extension citation.  M3 or M4 growth requires the
census-correction citation.  M6 component growth also requires a census
correction while parser identities are unchanged.  M5 alias-count growth is
rejected unconditionally, and every alias must have a valid sunset.

After that ratchet passes, a public-census decrease is accepted.  Otherwise,
every raised low-consumer, co-occurrence, lonely-type, sugar-shaped, and due
alias-sunset flag needs a verdict in the latest `docs/tenkz/SHRINK.md` session.
The ledger is append-only: retain the entire pre-change file byte-for-byte as a
prefix and add corrections and verdicts in a new final session section.

A verdict is a table row whose first cell is the exact `flag:*` ID printed by
`flags` (escape an internal table pipe as `\|`).  Its second cell must begin
with one of `keep-because`, `keep`, `dies`, `demoted`, `folds`, `respelled`,
`becomes`, `moves`, `confirmed`, `confirmed merge`, `tombstoned`,
or `sugar preset` and include an unexpired `expiry <milestone>` or `permanent`
lifetime.  The alternative execution form must begin exactly
`executes at the <milestone> freeze`.  Prose outside such a row is not a
machine-readable verdict.

## Pre-1.0 contract and 1.0 evidence gate

`DESIGN.md` owns the package and event-stream contract.  `SOAK-1.0.md` is an
inactive ledger while its normative block says `enforcement = "pending"`.
During that state, no campaign entry is valid and reviewed follow-up PRs may still
correct the prefix.

Before the 0.9 freeze, do not preserve an obsolete spelling merely because it
exists today.  Move its callers to the clean 1.0 form in the same change, then
delete it.  Do not add an alias, compatibility reader, dual writer, or temporary
bridge.  If one pull request is too large, stack small pull requests whose
integration order keeps every merged tree on the single new contract.
The shrink ledger's `alias(...)` verdict records debt already present; it is not
permission to introduce another alias.

The activation slice under #5352 will add the validation commands here only
after their scripts, repository-evidence checks, tests, and CI wiring exist on
`main`.  Close both blocker groups before activation.  One
self-referential activation pull request then verifies the current no-update,
no-delete, no-bypass `tenkz-v*` protection and changes exactly seven scalars:
both normative enforcement values, the inventory's raw-blob digest, the Git
tree OIDs of `tests/tenkz/release-harness/` and
`tests/tenkz/release-support/`, the SHA-256 of the exact armed `DESIGN.md` UTF-8
blob, and its own pull-request reference.  It
cannot change the checker, workflow, inventory, either pinned tree, policy
prose, or any other byte.  A later self-referential freeze record validates the
tag-derived 0.9 payload and supplies the verified attempt-ordering anchor.

The policy's dedicated closed workflow list is pinned indirectly by the
activation integration.  Every later candidate and post-merge check requires
those exact workflow blobs and modes at its exact target, rejects a candidate
diff touching them, and binds an accepted GitHub run to the pinned workflow
bytes and head.  Local actions and reusable workflows join that
activation-derived object set.  External actions and called workflows use full
commit SHAs, containers use content digests, and interpreters, helpers,
packages, and runtime downloads join the recursive closure.  Package-manager or
downloader execution, an unhashed lock, a tag, branch, missing object, or
incomplete closure fails closed.  Network access is disabled before any
repository code or validation command runs.

Release-test code and imported or sourced helpers live under the dedicated
`tests/tenkz/release-harness/` tree.
Expected outputs, baselines, allowlists, thresholds, and other immutable
acceptance configuration live under `tests/tenkz/release-support/`.  The closed
inventory separates mutable product-program paths from non-executable fixtures; the
program may be run only through the pinned harness, and neither role can select
coverage or supply runner, helper, or acceptance logic.  Each atomic test owns
one pinned assertion-failure fingerprint.  Commands run in the hermetic
repository-shaped view specified by `SOAK-1.0.md`, with a fixed output mount,
pinned child-tool profile, and no host-checkout or network access.  Symlinks,
submodules, special entries, and any other in-repository dependency fail closed.
These exact pins belong to the 0.9-to-1.0 campaign.  A later release gets a new
versioned policy and harness; it does not reopen this ledger or freeze 1.0 test
bytes forever.

The first actual campaign entry waits until the blocker chain recorded in the
policy has closed.  Its prerequisite list is the pinned policy chain flattened
in row-major order; `SOAK-1.0.md` does not own a duplicate list.  The source PR
needs an approval from a repository-authorized independent reviewer on its
exact final head and an integration tree equal to that approved tree.  The
tagged source integration and freeze-record
merge are atomic: `main` must not advance between them, or the unused tag is
abandoned and the source/tag step repeats with a patch larger than every
existing `tenkz-v0.9.*` tag, including one with no ledger entry.
The freeze entry stores the complete sorted tag-name snapshot seen by its exact
candidate check.  A later tag is a later reservation; it does not change what
that earlier check observed.

Once the freeze record lands, the evidence gate has no calendar delay.  It
requires two distinct, independently approved real-work pull requests merged
after the freeze: one changing a production Lean formalization (excluding
`TNLean/Archive/**`) or blueprint chapter or appendix, and one changing an RMP
benchmark case.  Immutable full pull-request diffs decide eligibility.  The
eligible source must still exist at the reviewed head, have a changed
comment-stripped token stream, and pass its class-specific Lean, blueprint, or
RMP validation.  Comment-only, whitespace-only, and deletion-only changes do
not qualify, and one pull request fills only one class.  Policy-, checker-, CI-,
ledger-record, and reset-receipt pull requests do not qualify.  Each record
pull request changes only its one ledger append.  A compatible-friction entry
records a nonempty list of pinned atomic tests for its public surface.  A
resolution names a separate exact-head-approved fix pull request: every test
reports its exact fingerprint at the friction and fix-parent trees, its fixtures
remain byte-identical, a declared surface-owned program changes, and the tests
plus full active-freeze payload pass at the fix head.
If no pinned atomic test witnesses a finding, or the frozen surface must break,
record `restart-required` and reset the attempt; do not disguise a broad failure
as compatibility evidence.  Release preparation lands only after every
compatible friction in the active attempt is resolved and both work merges have
landed; its exact diff changes only the tag-derived 1.0 manifest and four
canonical release artifacts.  Exact-head sign-off review follows immediately
on that integration; if `main` advances, repeat preparation on the new tip.  A
validated sign-off remains live until a full replay succeeds.  The dependent
publisher first reads the final ref.  It either constructs the one signed tag
object fixed by the release policy and creates an absent ref, or authenticates
that already-present object without reading the private key.  A retry never
invents a second object.  Do not push the tag by hand: any other object is an
incident, not a release.
Before its first write, the publisher verifies the candidate object's signature,
schema bytes, object ID, and peel.  A successful job is itself the API-visible
publication fact; there is no inaccessible job-output receipt.  Remove the
environment key after that success.  A later validation declares release only
after it sees the exact object, the historical pinned publisher job, and the
retired key.  Unrelated workflow files may then evolve without changing that
historical evidence.
Current mutable facts are replayed forever: drift before the final-tag ref uses
the reset process, while drift after that ref exists is a hard incident and
never reopens the ledger.

A valid `record-invalid` reset acknowledges its historical target, so the same
failed fact is not queued forever.  If that reset later becomes invalid, its
target is uncovered and both invalid records require later valid resets.
Historical placement is replayed from exact-head evidence bound to the reset's
pre-reset prefix.  The current audit always uses the actual final-prefix
boundary; a stale caller-selected boundary is rejected.
Before a `record-invalid` ledger append, a separate independently approved
receipt PR adds one canonical blob under `docs/tenkz/soak-replay/`, using the
schema in the pinned support tree.  The ledger-only reset names that PR and the
blob digest.  The reset and every later validation tree retain the exact blob.
Later replay reads that current-tree copy, so a rewritten old integration is
recoverable by restoring the same bytes; workflow artifacts and newly supplied
historical snapshots are not evidence.

The enforcement workflow must fail closed when GitHub evidence is absent,
null, incomplete, or inconsistent with the fetched Git objects.  Candidate and
post-merge checks need pull-request open, reopen, synchronize, ready-for-review,
and close activity; review submission, edit, and dismissal activity; issue
close and reopen activity; and pushes to `main` and the `tenkz-v*` tag
namespace.  It performs only read requests.  Its credential principal needs
read access to repository contents, pull requests, reviews, and issues, plus
the write-level ruleset visibility GitHub requires to return unredacted rule
and bypass details.  It also needs complete name-and-access visibility for
repository, organization, and environment Actions secrets; secret values are
never read.  Missing or redacted details fail closed.  Ruleset
administrators and the GitHub control plane are trusted; this current-state
check does not claim to detect an administrative protection gap restored before
the snapshot.  No live-entry or release command is available while enforcement
is pending.

## Shared parsers

`scripts/tenkzlib/tnlog.py` is the canonical schema-validating parser for
`.tnlog` event streams.  Use it whenever a checker needs structured event
fields.  Some narrow regression tests still inspect raw lines directly,
including `scripts/test_tenkz_cd_map_labels.py`,
`scripts/test_tenkz_enclosures.py`, and `scripts/test_tenkz_peps_torus.py`.
Before changing event syntax, field order, or validation, search every `.tnlog`
consumer and update or migrate these exceptions; do not assume the canonical
parser is their only dependency.
`scripts/tenkzlib/texcase.py` provides shared TeX comment stripping,
balanced-group matching, and picture-construct scanning.  Import these modules
when adding or modifying a checker that needs those answers.
Known local balanced-group parsers remain in
`scripts/tenkz_shrink.py::_group_payload` and
`scripts/tenkz_language.py::_group`; keep both aligned until they migrate to
`texcase.py`.  RMP case-header extraction remains local to
`scripts/tenkz_rmp.py`; do not claim it as shared until it moves into the
library.  Never add another parser for syntax already parsed by
`scripts/tenkzlib/`.

## Stage ownership

Each stage file begins with its declared input, output, owned-state, invariant,
and next-stage contract.

These are normative ownership rules for new code and migration destinations,
not a claim that every historical path has moved.  The live `tenkz-core`,
`tenkz-grid`, `tenkz-cd`, `tenkz-lattice`, and `tenkz-free` files still combine
some parsing, geometry, rendering, and event work; direct `\draw` or `\node`
emission in those files remains migration debt.

- `tenkz-model.code.tex` owns normalized semantic records and freezes topology
  after validation.
- `tenkz-metric.code.tex` owns the motivated metric registry and its sole
  dimension accessor.
- `tenkz-geometry.code.tex` owns frames, placement resolution, directions, and
  silhouette support distances; it emits no ink.
- `tenkz-render.code.tex` owns final mark and string emission from frozen
  records and resolved geometry; it parses nothing and stores no topology.
- `tenkz-string.code.tex` owns saved string paths and the crossing, join, and
  gap ledgers consumed by rendering.

The string stage has one further explicit exception: until string/render
integration is complete, string fixtures use the temporary
`\__tenkz_string_dev_draw:nn` primitive in `tenkz-string.code.tex`, which issues
the development `\draw` directly.

Read the header before changing a stage, and keep new state in the stage that
owns its answer.

## Pull-request evidence

Every change under `tex/tenkz/` records both semantic and visual evidence in
the pull-request body:

```sh
scripts/tenkz_golden.sh --check
scripts/tenkz_pixelpair.sh origin/main
```

The golden gate proves event-stream parity for the top-level corpus fixtures.
Run the applicable suite-specific semantic gates for affected nested fixtures.
The same-session pixel pair proves render parity only for the fixtures listed in
`tests/tenkz/pixelpair-sources.txt`.  If a change can affect a fixture outside
that manifest, add the affected fixture to the comparison or attach reviewed
replacement render evidence.  If a reviewed contract or drawing intentionally
changes, state the affected fixtures and attach the reviewed replacement
evidence instead of claiming parity.

The demolition checker remains a temporary guard against restoring retired
catalogue paths and expires at the 0.8 close, after branches predating the
demolition have landed or died.  The pixel-pair command expires with the redraw
campaign at 1.0.

## Audit and visual review

After compiling, audit the exact event stream used by the rendering and lint
the source:

```sh
python3 scripts/tenkz_audit.py <job>.tnlog
python3 scripts/tenkz_lint.py <source>.tex
```

Render every affected PDF and inspect it.  Exit status is not visual review.

```sh
mkdir -p tmp/pdfs/tenkz
pdftocairo -png -r 200 -singlefile <file>.pdf \
  tmp/pdfs/tenkz/<name>
```

Inspect labels, clipped ink, crossings, region contours, paired pages, and
section transitions.  A meaningful geometry change requires a fresh render.
Generated PDFs and PNGs are build artifacts, not committed source.

## Source and event checks

- Each figure states `Formula`, `Ink`, `Boundary`, `Source`, and
  `Capabilities` in its source header where the corpus format requires them.
- Structural capability tags name the public construct that owns the picture
  model. A `\tenkzkernel` case therefore carries `kernel`, even when its
  renderer contains a nested `tenkz` environment; `grid` is reserved for the
  grid surface without the kernel wrapper.
- A diagrammatic equation has the intended boundary signature on both sides.
- A matrix keeps two open virtual indices, a doubled-space map keeps four,
  and a scalar keeps none.
- The applied channel is `[sandwich, east={cup=$X$}]`; a west cup feeds the
  adjoint.
- Canonical sources do not use aliases, private control sequences, raw
  `tikzpicture`, whole-figure macros, or undocumented coordinate escapes.
- `\tndeclareatom` declarations have complete typed ports.  There is no
  public `\tndefine` mechanism.

## Architecture checks

Before editing a stage, read its five-line contract.  Maintain the direction

```text
language -> model -> style/atoms -> geometry -> dialect layout -> rendering -> events
```

Validation ends before measurement.  Rendering neither parses user syntax nor
changes topology.  Public names come from the executable registry; private
names follow `\__tenkz_<owner>_...:`.  Unsupported requested ink is a coded
error, never a warning followed by omission.

Until the S4 surface swap, kernel package loading is inert with respect to the
0.7 surface. `KERNEL-LOAD-SWEEP.md` records the binding and key-tree audit and
the regression that protects this boundary.

## expl3 and PGF traps

These mistakes have shipped bugs here.

1. Never expand `\q_no_value`.  Use the house accessor or a TF form of
   `\prop_get`.
2. Integer factors sit to the right of `*` in `\dimexpr`; prefer
   `\dim_eval:n`.  Do not put a leading decimal factor before a dimension
   macro in a pgfkeys value.
3. Double parameter tokens inside nested inline mappings: `##1` in the body
   of an `\int_step_inline:nnn` defined by another macro.
4. Normalize integer registers with `\int_eval:n` before using them as
   property keys.
5. User-input colons have catcode 12.  String-normalize before parsing
   `rows=`, `ports=`, and similar delimited forms.
6. `\use:e` passes `#` literally; do not double it there.
7. PGF keys split at literal commas and an unbraced value can be truncated at
   a second equals sign.  Brace values containing either character.
8. Expand integer registers explicitly in `\iow` event writes.
9. Picture IDs nest: the global UID and group-local current ID have different
   ownership.  An inline `\tnpic` must not clobber its parent.
10. `\prop_new:N` builds a flat store: `\prop_get`, `\prop_if_in` and
    `\prop_item` all compare the wanted key against every other key, so a
    store the picture fills costs the square of its size to read.  Declare
    such a store with `\__tenkz_prop_new_indexed:N`, which answers a key in
    one step.  A pair-keyed store — one entry per pair of routes — is the
    worst case and must never be flat.

## Geometry discipline

One base pitch controls the metric.  Repeated dimensions are named ratios.
Clearance uses the measured silhouette plus the single daylight separation;
do not add a constant that predicts what another pass will draw.

Useful focused regressions include:

```sh
python3 scripts/test_tenkz_face_ports.py
python3 scripts/test_tenkz_label_overlap.py
python3 scripts/test_tenkz_enclosures.py
```

Run the focused test while iterating, then the affected corpus or benchmark
section, then the repository gates appropriate to the change.

### RMP dimension inventory

The RMP driver applies two dimension checks before compiling any target.  The
aggregate ownership ratchets reject increases, unowned or commented case
dimensions, and benchmark-book allowlist drift.  The version-5 inventory in
`tests/tenkz/rmp/dimension-ownership.json` additionally freezes every active
literal at its semantic owner site.  Each case first lists its executed PICTURE
scopes.  Public tenkz environments, `tenkzeq`, and `tngroup` receive
hierarchical, per-parent source-order anchors even when their bodies contain no
dimensions.  The construct list records the drawing constructs: picture
environments, `tnpic`, and `tntree`.  A nested drawing's anchor includes its
PICTURE ancestry.  Command and drawing-container invocations are anchored
beneath their owning drawing; dimension-free commands and semantic starred
variants still receive source-order anchors.  `tenkzeq` is recorded only as a
scope.  It may precede the first drawing, and therefore has no honest drawing
owner.  An invocation's identity includes the exact PICTURE scope in which it
executes.  Dimension-bearing rows reference the exact owning invocation and
carry a comment-independent, TeX-token-normalized command or option skeleton.
Every option skeleton also
includes the registry-validated environment or command that owns it, so moving
a value between compatible option containers, same-name sibling invocations,
or PICTURE scopes changes the site identity.  Scopes, constructs, and
invocations stored in inert macro bodies are excluded by the same execution
mask as dimension ownership.
Owned values use `<dimension>` markers one-for-one with their literal vector;
dimensions belonging to a narrower nested site use `<nested-dimension>` and
are counted only by that nested owner.
Structural option separators and comment splices do not change a skeleton, but
significant whitespace inside argument token lists and option values does,
including nested bracket values.  Authored marker punctuation is escaped before
generated dimension placeholders are inserted.  Only repeated identical
skeletons receive a local occurrence number.  This catches a balanced
replacement or cross-site move that leaves all aggregate counts unchanged.

After an intentional, reviewed migration, update that exact inventory with:

```sh
python3 scripts/update_tenkz_dimension_inventory.py
python3 scripts/test_tenkz_dimension_inventory.py
```

The updater runs the aggregate ceilings before writing, rejects a malformed
old inventory, prints the site-level diff and the
case/scope/construct/invocation/site/dimension totals, and is byte-idempotent.
Do not edit the inventory to make an unexplained movement pass.  Comment
literals and the benchmark-book layout allowlist stay under their existing
orthogonal ratchets and never appear in these case rows.

## Historical design records

Superseded design proposals, migration inventories, reviews, and 0.6
worklists live under `docs/tenkz/history/`.  They explain earlier decisions but
do not define current syntax.  Do not revive a spelling from history without
passing the extension gates in `LANGUAGE.md`.
