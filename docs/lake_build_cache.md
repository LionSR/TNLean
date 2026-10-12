# Reusing a local Lake build

Fresh worktrees can reuse an existing TNLean `.lake` without sharing writable
build directories. The seed command uses APFS copy-on-write cloning:

```bash
git worktree add -b agent/my-branch /private/tmp/tnlean-my-branch origin/main
scripts/seed_lake_build.sh /private/tmp/tnlean-my-branch --dry-run
scripts/seed_lake_build.sh /private/tmp/tnlean-my-branch
```

The source defaults to the repository's primary worktree. Pass another source
worktree as the second argument when needed:

```bash
scripts/seed_lake_build.sh TARGET_WORKTREE SOURCE_WORKTREE
```

The command requires both paths to belong to the same repository, identical
`lean-toolchain`, `lake-manifest.json`, and `lakefile.toml` files, an existing
regular, non-symlinked source `.lake`, `.lake/build`, and `.lake/packages`
directories, and an absent target `.lake`. Git dependency checkouts must be
clean and at the revisions recorded in `lake-manifest.json`; nested Lake build
directories must not be symlinks; and Mathlib's prebuilt `Mathlib.olean` must
already be present. If it is missing, run
`scripts/lake_build_locked.sh -- lake exe cache get` in the source worktree
before seeding. The seed command also runs `lake exe cache get` itself
to verify that the prebuilt artifacts match the current manifest revision.
macOS `/bin/cp -c` creates independent writable files and fails instead of
falling back to a full copy when APFS cloning is unavailable. The absolute path
keeps Homebrew GNU coreutils from shadowing the APFS-aware command. Do not seed
while the source worktree is running a Lake command. The target `.lake` is an
inaccessible reservation until the completed clone is atomically swapped into
place, so a target Lake process cannot observe a partial cache.

TNLean build artifacts are reused only when the source and target worktrees are
at the same Git commit. If their commits differ, the command seeds only the
validated dependency packages, including prebuilt Mathlib artifacts, and
leaves the target without `.lake/build`. This prevents Lean from loading stale
TNLean `.olean` files whose declarations no longer match the target source.

At an identical commit, run the desired command through the build wrapper and
Lake will reuse the full build. After a cross-commit seed, run
`scripts/lake_build_locked.sh` first so TNLean is rebuilt against the seeded
dependencies. For a targeted check that applies the package `leanOptions`,
including the Mathlib standard linter set, run
`scripts/lake_build_locked.sh TNLean.Path.To.File`. Linter diagnostics
appear only when Lake re-elaborates the module; an unchanged, already-built
module produces no new diagnostics. A bare
`lake env lean TNLean/Path/To/File.lean` remains useful for fast elaboration,
but it does not apply those package options and is not a linter-bearing local
verification.

## Serialize local builds

The seed command and the build wrapper acquire a blocking BSD file lock through
Python 3's `fcntl.flock`, using one lock file in Git's common directory. Descriptor
9 remains open in the command and its children. This serializes cooperating
commands across TNLean worktrees without sharing writable package checkouts:

```bash
scripts/lake_build_locked.sh
scripts/lake_build_locked.sh TNLean.Path.To.File
scripts/lake_build_locked.sh -- lake build -q --log-level=info
```

Without `--`, the wrapper fetches the pinned prebuilt cache before building.
The `--` form runs exactly the supplied command. Direct `lake` commands bypass
the lock, so use the wrapper for local TNLean builds while another worktree may
be warming or seeding its cache.

To refresh the canonical cache and seed an issue worktree, use regular,
self-contained package directories throughout:

```bash
git -C worktrees/hot-main fetch
git -C worktrees/hot-main reset --hard origin/main
(cd worktrees/hot-main && scripts/lake_build_locked.sh)
scripts/seed_lake_build.sh worktrees/issue-N worktrees/hot-main --dry-run
scripts/seed_lake_build.sh worktrees/issue-N worktrees/hot-main
```

## Sort build timings

Save a build log and list every job taking at least 25 seconds:

```bash
scripts/lake_build_locked.sh -- lake build 2>&1 | tee /tmp/tnlean-build.log
python3 scripts/lake_build_hotspots.py /tmp/tnlean-build.log
```

The report is tab-separated and sorted from slowest to fastest. It exits
unsuccessfully if any reported job takes at least 50 seconds. Use
`--warn-threshold` and `--error-threshold` to override these limits.

Pull-request CI applies the same policy only to changed Lean files: 25 seconds
creates a warning annotation on the file, and 50 seconds fails the separate
`compile-time` job. Timings are local diagnostic evidence, not benchmarks
comparable across machines.

Lightweight tests do not run Lean. The shell integration test is macOS-only
because it exercises the APFS clone operation, so run it manually on macOS:

```bash
python3 scripts/test_lake_build_hotspots.py
scripts/test_seed_lake_build.sh
```

## Main CI cache production

`pr-ci.yml` keeps one running workflow and at most one pending workflow per ref.
New pushes to `main` replace the pending run without cancelling the running
one, allowing it to reach the successful-build cache save despite frequent
merges. Manual dispatches on `main` share this policy and group. Pull requests
and dispatches on other refs still cancel superseded running workflows.

This can delay checks for the latest main commit until the running workflow
finishes; it does not guarantee a build for every intermediate commit or make
a failing build save a cache. Cache keys still identify the built commit and
all three root inputs. The cache guards and full build requirements below are
unchanged.

## Narrow compatible-main CI seed

The ordinary `pr-ci.yml` cache key and restore prefix still hash all three root
inputs: `lean-toolchain`, `lake-manifest.json`, and `lakefile.toml`. Only a
successful main build saves the same four build directories; Mathlib's prebuilt
retrieval remains separate. Both the requested and matched cache keys are logged.
A false `cache-hit` is **not** a miss: a nonempty `cache-matched-key` means the
ordinary prefix restore already succeeded and disables the fallback.

On a genuine miss, `scripts/ci_compatible_cache.py` can reuse dependency artifacts
across one narrowly validated kind of QICLean revision update:

- Freeze `origin/main` and inspect at most 64 first-parent commits, independent of
  the PR base. This handles stacked PRs and a main push that changed the pin.
- Require byte-identical toolchains, known root manifest schema, and identical
  complete resolved dependencies except QICLean's `rev`/`inputRev`. Parsed root
  TOML may differ only in QICLean's revision, including identical weak options.
  Both QIC revisions must be full immutable commit IDs; URL, name, subdirectory,
  package options, and every other dependency remain unchanged.
- Read both immutable QIC trees. Its own toolchain, configuration, and dependency
  manifest must be identical. Existing proof source must be unchanged: only added
  modules, added imports in pure aggregators, and documentation edits qualify.
  Removals, renames, metadata changes, and unknown changes refuse the seed.
- Use `hashFiles` on the baseline's original three files, then perform a
  **lookup-only** request restricted to that exact full-input prefix. Never use a
  broad `tnlean-build-` or toolchain-only prefix.
- Require one unambiguous, exact, main-scoped REST record for the lookup match.
  Its archive version witnesses the lookup action's paths/compression match.
  Try that key first, then exact keys from the same frozen 64-commit main window.
  Every candidate must have byte-identical baseline inputs, the same archive
  version, one unambiguous main-scoped cache record, and a completed main push
  workflow with a successful build/save on `ubuntu-latest`. Verify the original
  save key/path/policy at each candidate commit. Refused candidates are skipped
  before restoration; no completed candidate means ordinary uncached operation.
  The [REST key filter](https://docs.github.com/en/rest/actions/cache#list-github-actions-caches-for-a-repository)
  can also match prefixes, so require exact equality and a single result across
  all refs/versions. Never filter out branch shadows or perform an unbounded scan.
  The [archive version](https://github.com/actions/cache#cache-version) binds paths
  and compression; missing or ambiguous lookup evidence refuses the fallback.
  Metadata uses public, unauthenticated REST reads, without a token or permission
  changes. The current runner must be Linux/X64. API errors refuse reuse without
  retries or a broader search.
- After the normal toolchain/Mathlib setup, restore only the selected exact key.
  Check the match, archive version, and provenance again before use. Postrestore
  refusal stops the job before pruning or building, without trying another cache.
  Run/job refusals log public IDs, attempts, source/status/platform values, and
  cache-save step results so inconsistent metadata can be diagnosed. A mismatch,
  partial restore, or pruning failure never permits direct Lean tests.

The fallback deliberately discards the cross-commit TNLean build. It also removes
QIC aggregator artifacts, modules outside its root aggregator closure, dependency
artifacts without tracked source, and unknown/executable outputs. Package
checkouts must match the root-resolved immutable revisions and have no tracked
changes. This prevents historical or removed unreachable modules from satisfying
regression imports. Unchanged QIC proof artifacts and unchanged Gametheory and
checkdecls modules remain reusable; no `.trace` or `.hash` is rewritten.

The ordinary full `lake build`, linter target, and all existing checks still run
before direct Lean regressions. The guard verifies that the default TNLean root
imports `QICLean`, ensuring its aggregator closure is rebuilt normally. This is
an optimization candidate, not evidence of a cache hit or measured speedup. It
does not relax `seed_lake_build.sh` or the stricter local seeding policy.

Run the no-Lean tests with:

```bash
python3 -m pip install PyYAML==6.0.3
python3 scripts/test_ci_compatible_cache.py
```

The optional dependency-free invalidation experiment is separate from those
parallel-safe tests. With the pinned Lake executable and an explicitly granted
exclusive Lean slot, run:

```bash
python3 scripts/test_ci_cache_lake_invalidation.py --lake /absolute/path/to/lake --sole-lean-slot
```

It creates disposable tiny projects and serializes targets to check unchanged
reuse, upstream/dependent invalidation, independent reuse, missing traces, broken
source rejection, and refusal of removed modules with surviving artifacts. It
never builds or edits TNLean, QICLean, Gametheory, or Mathlib caches.

### Early builds and strict checks of changed files

After cache setup and provenance pruning, the `build` job runs
`scripts/ci_lean_checks.py early`, a fail-fast Lake build of the production
modules changed by the pull request, so their failures surface before the root
build. After the root build, `scripts/ci_lean_checks.py strict` elaborates the
changed production files and every affected `TNLeanTest` file with warnings as
errors. Test objects go to a fresh overlay that precedes every Lake package path,
so a test may import another test without reading a stale production artifact.
See `docs/ci-automation.md` for the selection rule.

The collared open-boundary check follows the same provenance pruning and
explicit Mathlib cache guard. Its fail-fast Lake target is
`TorusDualOpenDeformation`, the sole regression import, so all four new production
modules and their complete import closures are rebuilt before strict elaboration.
The regression prints eight axiom audits; `check_collared_open_axioms.py` requires
all eight and rejects every axiom outside `propext`, `Classical.choice`, and
`Quot.sound`, including `sorryAx`. All other direct Lean regressions remain after
the full root build. No dependency pin or artifact provenance rule changes.
