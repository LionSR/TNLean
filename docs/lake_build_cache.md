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
source `.lake/build` and `.lake/packages`, and an absent target `.lake`.
`cp -c` creates independent writable files and fails instead of falling back
to a full copy when APFS cloning is unavailable. Do not seed while the source
worktree is running a Lake command.

After seeding, run the desired `lake build` or `lake env lean` command. Lake
will reuse unchanged artifacts and rebuild files changed on the branch.

## Sort build timings

Save a build log and rank jobs above a chosen duration:

```bash
lake build 2>&1 | tee /tmp/tnlean-build.log
python3 scripts/lake_build_hotspots.py /tmp/tnlean-build.log \
  --threshold 30 --limit 25
```

The report is tab-separated and sorted from slowest to fastest. Timings are
local diagnostic evidence, not benchmarks comparable across machines.

Lightweight tests do not run Lean:

```bash
python3 scripts/test_lake_build_hotspots.py
scripts/test_seed_lake_build.sh
```
