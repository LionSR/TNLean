# Selective OpenAI source and build audit (#8741)

This batch establishes reproducible **source import closures**, source hashes,
regression signatures, candidate reuse boundaries, and failed cache-first build
attempts. It ports no Lean proof. No OAI proof module, downstream production module,
or exported axiom closure was compiled or verified. The cache executable itself
compiled; that is tooling evidence only. #8741 remains open.

Source: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`, the September 24
manuscript baseline. TNLean comparison base:
`b7a0184ce22b29102fe17a6e96a9ba83b98d5510`. The fetched main revision during this
audit was `044dff82f778ab73d603355c68d773d4a714c3c6`; its changes from the base are
unrelated MPU modules/blueprint, which this batch does not touch. Dependency pins
and the MPU-gauging exclusion are preserved.

## Deliverables and meanings

- [Source manifest](../provenance/openai-math-port-manifest.json): immutable Git
  blobs and SHA-256 hashes, imports, dependency-first orders, lexical declaration
  anchors, exact root signatures, expanded `OneCopyMoveBound`, configuration and
  lockfile records. Generated from Git objects, independent of working-tree edits.
- [Reuse boundaries](../provenance/openai-math-reuse-boundaries.json): reviewed
  candidates, repository ownership, restrictions, and existing QICLean anchors.
  Every decision remains deferred; no candidate is labelled replaced or ported.
- [Build audit](../provenance/openai-math-build-audit.json): exact commands, cwd,
  revisions, environment overrides, exit codes, elapsed time and compressed raw
  logs. The recorded log SHA-256 is for the **decompressed** bytes.
- `scripts/audit_openai_closure.py`, `prepare_openai_baseline.py`, and
  `run_openai_build_audit.py`: regeneration, disposable baseline construction,
  and bounded cache-first verification. Fifteen passing unit tests exercise graph failures,
  immutable reads, manifest consistency and rejection of failed cache gates.

| Root under `OAI.MathematicalPhysics` | OAI module closure |
|---|---:|
| `PEPSFilters.GeometricOptimizer` | 25 |
| `PEPSMove.PhysicalMove` | 33 |
| `PEPSSubvolume.Subvolume` | 51 |

The union contains 107 modules and 24,129 source lines; its only explicit external
import is `Mathlib`. Subvolume shares `PEPSFilters.Basic` and `LocalOperators` with
the optimizer closure. `PEPSSubvolume.Main` and `TensorNetwork.VectorColumn` are
outside the union. These are the minimal closures **under unchanged module
imports**, not minimal declaration/proof dependencies. The manifest does not
resolve elaborated names, generated declarations, implicit typeclass dependencies,
or kernel axioms. Its lexical forbidden-token scan found no occurrences after
masking comments and strings; this does not substitute for `#print axioms`.

## Original-pin baseline and migration status

| Component | Upstream baseline | TNLean |
|---|---|---|
| Lean | `v4.34.1` | `v4.35.0-rc3` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` | `c55e6e786f49471c72fbddbec5415808896aec1e` |
| QICLean | Not required by selected source | `8d5389d23c8e675a0117442e1a0d2c683a4bad41` |

Elan installed in `/workspace/elan`, but both `elan toolchain install` requests
failed with `CONNECT tunnel failed, response 403`. Official GitHub release asset
downloads succeeded. Both extracted binaries report the intended versions.
No toolchain version was substituted.

The original upstream `lean/lakefile.lean` declares many unrelated projects and
runs dependency-clone/patch logic during configuration. The disposable baseline
therefore retains only the selected unchanged source files and Mathlib's exact
locked dependency closure. Its generated Lake configuration preserves upstream
`autoImplicit = false` and adds `weak.linter.mathlibStandardSet = true`. The
original package configuration is hashed in the manifest, but was **not run**.
This is a reduced original-pin baseline attempt, not a successful build of the
original full Lake package. It never changes the source checkout, vendors files
into TNLean, or changes TNLean's Lake configuration.

The first `lake exe cache get` attempts resolved dependencies and built the cache
executable, then failed on the read-only `/home/agent/.cache/mathlib` (exit 1).
Retrying with separate writable `MATHLIB_CACHE_DIR` directories reached the default
cache service but every observed transfer failed with CONNECT 403. Both retries
were bounded at 300 seconds (exit 124). A direct probe of the documented legacy
Azure endpoint also returned CONNECT 403; no Azure cache build was claimed.
No `Mathlib.olean` exists in either package cache. The build runner therefore ran
no `lake build` and no axiom commands, as required by the cache policy. These are
access failures, **not Lean source incompatibilities**. No Mathlib API adaptation
has been tested, and no timing conclusion about proof elaboration follows.

## Selective reuse conclusions

`PEPSFilters.Basic` mixes finite-grid/support definitions with ground-state/gap
predicates, contraction, and unproved headline predicates. Copying that file is
not a foundations milestone. Coordinate canonical physical definitions with
#8738, contraction with #8740, and generic gap/entropy equivalences with #8739.
`LocalOperators` has a two-module source closure, but its region lifts still
need comparison with those canonical interfaces.

`CollarWeights` is a Mathlib-only arithmetic leaf. `Subvolume.power_bound` is a
generic recurrence-to-real-power argument trapped in a 51-module import closure.
Both belong in QICLean (or Mathlib), despite upstream physical namespaces. The
integer-division lemmas at the beginning of `RectangleTiling` should likewise be
separated from physical finite-square tilings. None is an excuse for a new
TNLean-local generic theory.

Existing candidate replacements include QICLean's `vonNeumannEntropy`,
`Matrix.partialTraceRight`, `Matrix.partialTraceLeft`, and
`Entropy.strongSubadditivity` at the exact companion pin. The reuse JSON hashes
the corresponding source files. The SSA interface uses finite product indices
and a PSD unit-trace matrix. Regional configuration reindexing, normalization,
and equality of entropy definitions must be proved before declaring a replacement.
Those bridges remain coordinated with #8739, not taken over here.

The optimizer regression retains positive parameters, normalized unique ground
state/full-system gap, rectangle and nearest-neighbor assumptions. The move
regression retains a normalized physical state, three pairwise-disjoint regions,
PSD trace-at-most-one inputs, and positive small exponent. The subvolume result
quantifies over **some parameter-dependent** exponent in `(0,1)` and square
boxes; it uses explicit normalized eigenvector and gap hypotheses. It does not
prove arbitrary domains/range, freely chosen exponent, the manuscript's final
`2·10^-6` exponent, boundary area law, or polynomial PEPS.

No independent unclaimed physical port was validated: small independent leaves
are generic, while physical foundations overlap active #8738/#8740 work and
require the #8739 interfaces. #8761 fidelity, #8762 VectorColumn, #8763 truncation,
#8764 routing, and #8768 effects retain their owners.

## Reproduction

Clone upstream into a separate directory. The manifest reads the fixed revision,
so no checkout mutation is required. Commands below assume this audit's workspace
layout and official toolchain archives have been extracted into `/workspace/toolchains`.

```bash
python3 scripts/audit_openai_closure.py --upstream /workspace/openai-math --check
curl -fLsS https://raw.githubusercontent.com/leanprover-community/mathlib4/d13f23b723b8a846827a245b89c10fc7d3f11612/lake-manifest.json -o /tmp/upstream-mathlib-manifest.json
python3 scripts/prepare_openai_baseline.py --upstream /workspace/openai-math --destination /workspace/oai-baseline-reproduction --mathlib-manifest /tmp/upstream-mathlib-manifest.json
MATHLIB_CACHE_DIR=/workspace/mathlib-cache-original python3 scripts/run_openai_build_audit.py --worktree /workspace/oai-baseline-reproduction --lake /workspace/toolchains/lean-4.34.1-linux/bin/lake --output /workspace/reproduction-original --timeout 300 --target OAI.MathematicalPhysics.PEPSFilters.GeometricOptimizer --target OAI.MathematicalPhysics.PEPSMove.PhysicalMove --target OAI.MathematicalPhysics.PEPSSubvolume.Subvolume --axioms AuditAxioms.lean
MATHLIB_CACHE_DIR=/workspace/mathlib-cache-downstream python3 scripts/run_openai_build_audit.py --worktree /workspace/TNLean --lake /workspace/toolchains/lean-4.35.0-rc3-linux/bin/lake --output /workspace/reproduction-downstream --timeout 300
python3 -m unittest discover -s scripts -p test_audit_openai_closure.py -v
python3 scripts/generate_import_aggregators.py --check
python3 scripts/check_forbidden_lean_tokens.py --base-ref origin/main
```

The baseline generator rejects an existing destination or a destination inside
TNLean. It verifies the Mathlib manifest bytes against SHA-256
`8f67b2cf24143ac091cdb425e886c2164b2fc2d6fbccd6db9454b697f9541a67`, independently
compared to the Git object at the locked Mathlib revision. All staged OAI files
remain byte-identical; a staging manifest records every source/configuration hash.
The runner prepends the selected Lake binary directory to PATH, records explicit
cache overrides, and never builds after a failed cache command or absent sentinel.
The downstream command intentionally requests only cache readiness: no target
port exists. Add actual reviewed downstream targets only in a later port batch.

## Provenance and remaining gates

Root `LICENSE` and `lean/LICENSE` are identical Apache-2.0 files with SHA-256
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.
No tracked NOTICE file was found at the source revision. The selected module
headers contain no copyright/author/SPDX notice matches. The temporary baseline
retains the source bytes and upstream Lean license. No upstream proof text is
introduced into TNLean production modules.

#8737 owns policy/schema validation. Coordination comments:
[initial boundary](https://github.com/LionSR/TNLean/issues/8737#issuecomment-6033330701),
[shard direction](https://github.com/LionSR/TNLean/issues/8741#issuecomment-6033338016),
and [no invented mappings](https://github.com/LionSR/TNLean/issues/8737#issuecomment-6033499900).
The future `docs/provenance/openai-math.d/8741.json` is reserved for real downstream
declaration mappings; this audit does not fabricate them. Source signatures in
the inventory are attributed by immutable source URL and hash.

Remaining acceptance gates are successful cached original-pin root builds,
reviewed minimal declaration dependencies, canonical interface/equivalence
bridges, selective downstream linter-bearing builds, and kernel axiom audits.
`AuditAxioms.lean` is generated for the three original roots. Gap and exact
contraction bridge audits must use the actual declarations from their owners;
no fictitious bridge is generated here. No blueprint completion tag is added.

The generated baseline was reproduced into a second empty directory; its complete
source/configuration staging manifest compared byte-for-byte equal. Manifest
regeneration, import-aggregator completeness, forbidden-token policy and
`git diff --check` also passed. Workspace `.agents` contained no skill files;
repository instructions were supplemented by `lean-conventions` and
`lean-build-cache` from `texra-ai/texra-lean-skills` at
`0c7bacce2ed86f5731e273a45272f8d400a09575`.

OpenAI Codex (GPT-6) produced the scripts, tests and audit text under the user's
assigned #8741 scope. Mathematical review and any merge remain with the human
maintainer. No merge or deployment is authorized by this batch.

## Separate GitHub original-pin validation route

Follow-up on #8785 adds `.github/workflows/openai-selected-baseline.yml`, triggered
only by changes to its workflow, the OpenAI audit scripts or source manifest, and
available for manual dispatch. This uses ordinary GitHub-hosted runners with
`contents: read`, no persisted checkout credentials, and no cache upload. It does
not change local network policy or use a different Mathlib cache source.

The job retrieves the immutable source objects, checks the manifest, constructs
the external baseline, verifies the audited SHA-256 of the official Lean 4.34.1
archive, and fetches the official prebuilt Mathlib cache. After the sentinel, it
runs `lake --no-build build +Mathlib:leanArts` and aborts if dependency artifacts
are stale. Only then may the three exact OAI roots build with the baseline's
linter options. No full OAI package or TNLean production source is imported.

After successful builds, the generated `#print axioms` output is checked against
an exact root-name set and the allowlist `propext`, `Classical.choice`, `Quot.sound`.
Missing/duplicate roots, `sorryAx`, custom axioms, or a failed command fail the
job. This kernel-axiom gate does not assert mathematical source faithfulness.
Source/configuration integrity and locked dependency revisions are checked again
after the attempt, including failures. Logs, hashes, CI revision/run identifiers,
the source staging manifest, and upstream license are retained as a 14-day
artifact. No evidence status in the original local-failure audit is overwritten.

CI artifacts are explicitly **original-pin baseline evidence**, never downstream
port evidence. No reviewed downstream proof port exists in this PR. The local
unit suite now also tests stale-cache refusal, axiom allowlist failures and
source-integrity mutation detection; execution outcomes will be linked on #8785.
