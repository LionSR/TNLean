# Canonical Interaction final validation and release gate

This is a read-only release assessment, not merge approval. No existing PR or production branch was modified.

## Frozen versions

- Validated final production source: 42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d, QIC 729428582b78ab7529b3796099193649f947354a.
- Shared #10881: fa9a40e22fa6384ba4a723e8bf675bb2cd20c5e7, an ancestor of final source.
- Refreshed main: 16b1dfbd7e45f0e8fed7f2607e25313cf5a9f931.
- #10905 head unchanged: 592a46e4e442f87205c407720acbb487db0d2fcf; merged at 2026-11-18T17:59:07Z as 0b469c1e2a4bab698d8fbac89107f13482a40d5d. Main then added #10908's dimension-dependence audit. Main retains QIC pin729.

## Existing validation boundary

107 PEPS / six shared owners / five fixtures have original successful execution records and full transitive source fingerprint reuse to 42c4. They were not recompiled in this assessment. See evidence cd2ae947 and its final-reuse-all.json. Snake newly compiled and strict-checked at exact42c4, with ten authorized prerequisite compilations; evidence ac7ad607. This duplicate cross-environment cost is explicitly preserved. MPS77 and the 25-module reverse closure remain external pending gates; no unreceived result is counted. The three MPS adapters are included in that 25; root aggregators require their own evidence, not inference from leaves.

Shared-to-final full manifest has 304 paths: 214 Lean, 52 audits, 38 other. This includes prior shared range restoration, five fixture paths and reviewed integration lanes; it is not 304 newly reviewed files in this turn. Final source relative to dccc has only the known three MPS adapter-removal files, and the worktree is clean. Complete manifests and exact patch are attached; this confirms no additional unrecorded delta since that review, not a fresh semantic review of all 304 paths.

## New integration blocker

Main is not an ancestor of42c4. Read-only git merge-tree --write-tree HEAD origin/main exits1 with 56 conflicting paths: 23 MPS, 27 PEPS and six documentation/Blueprint paths. Full index stages and conflict paths are attached. No conflict was resolved or staged. The generated merge-tree object is diagnostic only, not a publishable tree. Therefore simply fast-forwarding shared fa9 to42c4 after MPS completes would still leave an unverified current-main integration.

## One-update plan after local gates

1. Receive exact MPS77 execution records and 25-closure coverage, classify valid transitive reuse versus new executions; keep unsupported root results pending.
2. In a separate integration worktree reconcile current main with the validated final source. Resolve the 56 conflicts by preserving canonical Interaction ownership, arbitrary gap/norm/PSD/membership scope, arbitrary J and empty domains, total-Hamiltonian Hermitian assumptions, five complete fixtures, and main's new audit. Obtain semantic review of each conflict. Do not choose a whole side blindly.
3. Recompute source/dependency fingerprints at the resulting exact head. Recompile/strict changed conflict modules and their affected consumers/fixtures; reuse only unchanged transitive fingerprints. Rerun source-sync, prose/style and all-owner selector there. Existing42c4 checks are not the merge-result checks.
4. Re-fetch shared head and main. If fa9 is still the shared head and the reviewed candidate descends from it, perform one ordinary fast-forward push of the completed candidate to the shared branch, with explicit coordinator authorization. Never force-push over concurrent work. If either ref changed, reconcile before publishing.
5. Record the new exact head and CI run; require current-head CI and substantive review before any merge decision. #10881 run44350615844 still has its fa9 build in progress and cannot validate42c4 or a future merge result.

The old source-sync976-missing failure, prior overlay failure, transport restriction and original execution ledgers remain preserved. New successful checks do not erase those historical version boundaries. No cold/full library build or Blueprint PDF/web/checkdecls was run here.

## Fresh lightweight checks at42c4

- source-sync: exit 0, 114.435 seconds; exact command/cwd/stdout hash in commands.json.
- prose: exit 0, 11.706 seconds; exact command/cwd/stdout hash in commands.json.
- selector: exit 0, 10.577 seconds; exact command/cwd/stdout hash in commands.json.
- diff-check: exit 0, 0.109 seconds; exact command/cwd/stdout hash in commands.json.
- Blueprint roles: exit0; command and output hash in roles-command.json.
- Selector: all22 single-path cases passed (16 Lean owners, dependency manifest, five fixtures).
- Source-sync uses BLUEPRINT_SYNC_FETCH_DEPS=0 and matching pinned dependency checkouts exposed read-only through cache links. Python/package versions are in environment.txt.
