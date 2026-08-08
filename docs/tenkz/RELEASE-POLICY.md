# Releasing tenkz

One page: what 1.0 promises, what evidence a release must show, how versions
and tags are spelled, and how a spelling dies. `DESIGN.md` is the normative
compatibility and campaign contract and `SOAK-1.0.md` its evidence ledger;
where this page and `DESIGN.md` disagree, `DESIGN.md` governs. Two
requirements are stated here and nowhere else, marked **(this page)** below:
the standing-gate list must be green at the release head, and the render
evidence standard of #4183 applies to release work. Read this page before
every release step; read `DESIGN.md` before arming one.

## 1. The compatibility promise

1.0 freezes three artifacts, each already in the tree:

| Frozen artifact | Role | Authority |
|---|---|---|
| `docs/tenkz/manual2.tex` + `chapters2/` | the reader-facing contract (#4163: the manual is the contract) | `DESIGN.md` §TeX surface |
| `tex/tenkz/tenkz-language-registry.tex` | the machine inventory of environments, commands, and keys; `chapters2/generated-language-reference.tex` is regenerated from it and must agree with the manual | `DESIGN.md` §TeX surface; `HACKING.md` §Fast build loop |
| `tests/tenkz/golden-events.sha256`, `tests/tenkz/kernel/golden.sha256`, `tests/tenkz/kernel/golden-pixels.sha256` | behavioural pins for the `.tnlog` side contract; byte evidence, not a schema | `DESIGN.md` §Event surface |

Promised: topology, boundary meaning, labels, default semantic ink,
successful compilation of documented valid input, and the `.tnlog` event
surface under its own `major.minor` version (header spelling owned by
#4162/#4703). Not promised: raster bytes across engines and font revisions,
private control sequences, undocumented development probes (`DESIGN.md`
§TeX surface).

What each release class may change (`DESIGN.md` §Package versions):

| Release | TeX surface | `.tnlog` surface |
|---|---|---|
| 1.0.x (patch) | defect fix only: documented input keeps compiling, defaults and meaning fixed | byte-stable for unchanged input |
| 1.x (minor) | additive documented capability through the extension gate (`Extension-gate: #NNNN`, `LANGUAGE-1.0.md` §11); deprecation may begin | additive kind or optional field, with the event minor incremented and the reader accepting old and new |
| 2.0 (major) | removal of deprecated input, change of a documented default or meaning | breaking change, with the event major incremented |

Re-pin protocol for the pins (`HACKING.md` §Golden event streams and
§Same-session pixel pairs): re-pin event streams only when fixture sources
change or a reviewed contract change intentionally changes emitted events; a
behavior-preserving change must pass `scripts/tenkz_golden.sh --check` and
does not authorize a new baseline. An event change for unchanged input is
never a patch — it is at least a minor with the event minor incremented
(`DESIGN.md`, `[compatibility.*]`). Pixel pins re-pin only through
`scripts/tenkz_kernel_probes.sh --check` then `--snapshot`, with every
non-pixel probe passing first.

## 2. Release evidence

A `tenkz-v*` tag is created only by the campaign in `DESIGN.md` §The 1.0
freeze and evidence gate: freeze, two qualifying real-work merges (one
`formalization-or-blueprint`, one `rmp-benchmark`), friction resolution,
release preparation, sign-off, publisher tag. Nobody pushes a `tenkz-v*` tag
by hand. The campaign harness named by the policy —
`tests/tenkz/release-harness/`, `tests/tenkz/release-support/`,
`tests/tenkz/release-tests.toml`,
`.github/workflows/tenkz-release-policy.yml` — landed with the activation slice
of #5636 and runs per PR. It is not armed. `SOAK-1.0.md` still reads
`enforcement = "pending"`, so no campaign entry is valid and no release command
exists. Arming is a separate self-referential pull request whose complete diff
is the seven scalars in `SOAK-1.0.md`, and it may open only after the blocker
chain closes and the final-tag signing key lands
(`tests/tenkz/release-support/README.md`).

What the harness is: the closed inventory names one atomic compatibility
assertion per entry, each with its own failure fingerprint, and the supervisor
runs each one in a repository-shaped view holding only the pinned trees, the
inventory, the four canonical artifacts, and that entry's declared subjects. An
assertion passes by exiting zero and fails by writing the closed receipt and
exiting ten; the supervisor rejects every other outcome. The mount namespace
that hides the real checkout and the denial of network access before repository
code runs belong to the enforcement workflow, not to the supervisor, and the
armed workflow adds both.

**What `check_tenkz_policy.py` reports, and when that changes.** The checker
prints `evidence not-started (0 entries)` and will keep printing it until a
freeze entry lands. Read it as the campaign's state, not as a defect: while
`enforcement = "pending"` the ledger is closed to entries by construction, so
`not-started` is the only state a valid pending ledger can have. Three things
must happen, in this order, before it reports anything else:

1. the blocker chain closes — #4162, #4703, #4708, and #4163 remain open;
2. the arming pull request flips both enforcement values and pins the four
   digests, which moves the checker from a pending ledger to an armed one;
3. the first `freeze` entry lands, which is what makes the state
   `attempt-1-active`.

Step 2 alone is not enough. On an armed ledger the validator requires a
repository-evidence bundle, which the plain command-line entry point does not
build; the armed states are reachable only through the enforcement workflow,
which supplies the GitHub and Git evidence. So the bare command reporting a
live chain is not a milestone this or any other implementation change reaches —
it is the campaign having started. Until then the standing gates below, not the
ledger, are the release evidence.

**(this page)** The standing gates below already run per PR and must be green
at the exact release head:

| Gate | Command | Where it runs |
|---|---|---|
| registry and language check | `python3 scripts/tenkz_language.py check` | `pr-ci.yml`, `tenkz-shrink` |
| shrink ratchet | `python3 scripts/tenkz_shrink.py gate` (+ `test_tenkz_shrink.py`) | `pr-ci.yml`, `tenkz-shrink` |
| corpus compile and event parity | `scripts/tenkz_corpus.sh`; `scripts/tenkz_golden.sh --check` | `pr-ci.yml`, `tenkz-corpus` |
| kernel and string probes | `scripts/tenkz_kernel_probes.sh`; `scripts/tenkz_string_probes.sh` | `pr-ci.yml`, `tenkz-corpus` |
| corpus provenance, dimensions, render | `test_tenkz_corpus_provenance.py`, `test_tenkz_dimension_inventory.py`, `test_tenkz_corpus_render.py` | `pr-ci.yml`, `tenkz-corpus` |
| manual doc-test | `python3 scripts/tenkz_manual_doctest.py` | `pr-ci.yml`, `tenkz-corpus` |
| manual compile and event audit | `xelatex manual2.tex` twice; `python3 scripts/tenkz_audit.py manual2.tnlog` | `pr-ci.yml`, `blueprint` |
| picture-source lint and shared parsers | `python3 scripts/tenkz_lint.py`; `test_tnlog.py`, `test_texcase.py`, `test_tenkz_kernel_audit.py` | `pr-ci.yml`, `blueprint` |
| evidence-ledger validity | `python3 scripts/check_tenkz_policy.py` (+ `test_check_tenkz_policy.py`, `test_tenkz_policy_evidence.py`) | `tenkz-policy.yml` |
| release harness, inventory, and assertions | `python3 tests/tenkz/release-harness/selftest.py`; `supervisor.py check-inventory`, `run-all`, `check-readiness` | `tenkz-release-policy.yml` |
| migration guards | `python3 scripts/check_tenkz_dispositions.py`; `python3 scripts/check_tenkz_demolition.py` | `tenkz-demolition.yml`; both expire with the S4 migration (`HACKING.md` §Pull-request evidence) |

**(this page)** The render evidence standard is working agreement 5 on #4183,
restated in #4709's standing rules, and it binds release work: a claim of
visual inspection names the rendered file, the DPI, and what was checked, and
carries a second viewer's independent look. Exit status is not visual review
(`HACKING.md` §Audit and visual review). This applies to the
release-preparation pull request and to any qualifying work pull request that
touches a figure.

Where evidence lives: golden and pixel evidence in the pull-request body
(`HACKING.md` §Pull-request evidence); the pins under `tests/tenkz/`; RMP
verdicts in `tests/tenkz/rmp/verdicts.toml` under the bar in
`COSMETIC-GAP-BAR.md`; campaign records appended to `SOAK-1.0.md` with replay
receipts under `docs/tenkz/soak-replay/`; each tag's manifest at
`docs/tenkz/releases/<TAG>.toml` (`DESIGN.md`, `release_manifest_pattern`),
first written at the 0.9 freeze.

## 3. Versioning mechanics

The version string lives in one place:
`\ProvidesPackage{tenkz}[YYYY/MM/DD vX.Y.Z ...]` in `tex/tenkz/tenkz.sty`
(today `v0.7`). At a tag, the manual version, change record, and event-format
declaration must agree with it (`DESIGN.md` §Release tags).

The four canonical release artifacts (`DESIGN.md`, `release_*` values) are
`tex/tenkz/tenkz.sty`, `docs/tenkz/manual2.tex`, `docs/tenkz/CHANGES.md`, and
`docs/tenkz/TNLOG.md`. All four are in the tree; the release-preparation pull
request sets their version lines together with the manifest. `CHANGES.md`
follows the register of the 0.6 record at `docs/tenkz/history/CHANGES-0.6.md` —
a table of changed spellings, one motivated paragraph per decision, and the
mechanical migration per spelling. `TNLOG.md` is the event-format declaration:
it states the line syntax, the event kinds, what the reader enforces, and which
invariants only the writers hold. The in-band `major.minor` header it declares
does not exist yet and remains owned by #4162/#4703, so until that lands the
event surface is held by the golden digests rather than by version
negotiation.

Tags are `tenkz-vMAJOR.MINOR.PATCH`, annotated, never moved or reused. Bare
`vMAJOR.MINOR.PATCH` tags belong to the Lean toolchain
(`.github/workflows/create-release.yml`) and are a distinct namespace. Freeze
candidates are `tenkz-v0.9.PATCH` with a patch strictly above every existing
`tenkz-v0.9.*` tag; `tenkz-v1.0.0` is created by the pinned publisher job
after sign-off, never by hand (`DESIGN.md` §Release tags).

## 4. How a spelling dies

After 1.0, a documented spelling leaves the language in three recorded steps
(`DESIGN.md` §Deprecations, tombstones, and frozen twins; `LANGUAGE-1.0.md`
§10–11):

1. **Registry sunset.** A minor release moves the row to
   `alias(...; sunset=...)`, names the one replacement and the earliest major
   allowed to remove it, and keeps tests proving the old behavior. The
   warning never becomes an error inside the same major series.
2. **Ledger verdict.** The shrink session flags the alias and
   `docs/tenkz/SHRINK.md` records the machine-readable verdict row
   (`HACKING.md` §Shrink sessions); meter M5 rejects alias growth outright.
3. **Removal at the major.** One change migrates the remaining consumers and
   deletes the parser rows and registry rows together; the dead spelling
   becomes a `LANGUAGE-1.0.md` §10 tombstone, rejected by parser and linter
   with its migration, and the name is never reused.

The worked precedent is the S4 retirement (#4699): sunsets and verdicts
recorded in `docs/tenkz/SHRINK.md` ("dies at S4 ... expiry 0.9"), coverage
classified in `FIXTURE-RETIREMENT.md` and migration classes in
`DISPOSITIONS.md` before any deletion, then batches that each migrated a
family and deleted its keys, parser rows, and registry rows in the same
change (#5621 retired the cd front end, #5626 the free front end), with the
shrink gate ratcheting the census down and the demolition guard rejecting
resurrection. S4 ran before 1.0 and therefore cut clean, with no deprecation
period (`HACKING.md` §Pre-1.0 contract); after 1.0 the same mechanics run
with the minor-release deprecation clock in front.

When a successor cannot preserve the released surface at all, the escape
hatch is the frozen twin: the old library entry point stays installable
beside the new one in the same package, on the `quantikz`/`quantikz2` model —
not a per-command alias, a compatibility switch, or a silent change
(`DESIGN.md` §Deprecations, tombstones, and frozen twins).
