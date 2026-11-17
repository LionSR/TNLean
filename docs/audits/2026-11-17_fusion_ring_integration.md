# Integer fusion foundation: integration-conflict repair

## Exact snapshots and ownership

- PR: https://github.com/LionSR/TNLean/pull/10636
- Existing branch: `feat/8322-integer-fusion-foundation`.
- Verified feature head: `1c76cd088883d8d014bfc17f8930c97528178cea`.
- Common ancestor: `cbf482955f46f36c71c95ab1547b3cc86b6d58c2`.
- Initially inspected main: `71c1185e9352a3b5237b37a6840640751da6ca2d`.
- Refreshed integration main: `61f346a794e61b66dd0b198781019de7f9c746d8`.
- Main tree: `5401fba723608895d9e739f2985350ff63fc64b3`.

The PR branch remained at the same head throughout preparation. Main advanced
by one unrelated edit to `docs/campaign/mpu/issues.md`; the refreshed main tree
retains that edit. The feature head's tree is identical to the pre-existing
local foundation checkout, permitting exact three-way inputs without changing
that checkout or either follow-up mathematical branch.

## Actual conflict and resolution

The seven PR-changed paths were compared against the common ancestor and
current main. There is exactly one textual conflict, one hunk in the generated
`TNLean/MPS/Symmetry/MPOSymmetry.lean` aggregator: the feature's `BasedRing`
import and main's `BlockMixedMPO` / `BlockMixedMPOFusion` imports were inserted
at the same location. The Blueprint chapter and glossary merge cleanly.
Neither dependency manifest is part of the feature diff; there is no textual
dependency-pin conflict.

The current-main import generator first reproduced the exact main aggregator
from its module layout. After adding the three feature modules, it retained
all 114 main imports and added exactly `BasedRing`, `IntegerFusion` and
`IntegerNIMRep`. The layout check is not a compiler check. The regenerated
aggregator retains both BlockMixed imports and all other main imports.

The integration tree is based on the complete refreshed main tree and changes
only the original seven feature paths plus this handoff. All other main blob
identities, deletions and dependency files are retained. Deleted definitions
are not restored. The three proof files retain their exact verified blobs:

| File | Git blob |
| --- | --- |
| `BasedRing.lean` | `aee79766ed83c57abcc85c89a947e0ee35b8a444` |
| `IntegerFusion.lean` | `31000da9f089187646f7a8fcdf83bd1d48c18d1f` |
| `IntegerNIMRep.lean` | `aa4ed662ed503b73c64ba242af66d33187fed512` |

Their statements, explicit NIMRep unit hypothesis and output-row/input-column
orientation are unchanged. `Defs.lean` and `Dimension.lean` retain main's
exact contents. The mathematical follow-up branches and PRs #10641/#10695
are outside this repair.

## Dependency coherence

The repair inherits main's root and docbuild manifests and lakefiles byte for
byte: QICLean `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`, Mathlib
`625d8914199bc567cca9b91f90e8e5afafa5ae51`, and Lean `v4.36.0-rc1`.
The old feature pin `c4576824` is inherited history, not a feature edit.
The root lakefile requirements agree with the root manifest, and the current
manifest checker confirms root/docbuild agreement on all 13 shared packages.
The pinned QICLean manifest independently records the same Mathlib revision
and Lean toolchain.

PR #10761 was still open at `899c3fe0007b8cfc069659d80cf68725b958207b`
during inspection. This repair does not stack on that unmerged pin change.

## Validation and precise limits

- Three-way merge inputs are checked against their exact Git blob hashes.
- Generated imports retain all main modules and add only the three feature
  modules; no conflict markers remain.
- Every main line in the merged chapter and glossary is preserved. The
  feature's declaration links and labels are conserved.
- Current-main reader-facing prose checks pass on the added lines. Scoped
  mathematical-role checks pass for the merged Blueprint chapter.
- All 12 transitive TNLean module paths for the foundation resolve in current
  main plus the three feature additions. This is an import-path check only.
- Root lakefile/manifest checks and the root/docbuild manifest checker pass.

Local kernel verification was not possible: there is no accessible Lean or
Lake executable, no cached prebuilt Mathlib artifacts at the pinned revision,
and the managed runtime reports an enforced disabled network policy. Mathlib
was not rebuilt from source, and no different toolchain or dependency pin was
substituted. Successful CI run 43781810819 validates the old feature head only;
it does not validate this integration tree. Fresh exact-head Lean, strict,
full-library and Blueprint checks are required after publication.

## Publication and gates

The intended repair commit has the existing feature head as first parent and
the refreshed main snapshot as second parent, so updating the existing feature
branch is a fast-forward. Publication must use the expected old feature SHA
and stop on a competing branch update. Main itself is not changed.

The PR remains draft. Prior approval-review denials for its public description
and ready-for-review transition are not retried. No workflow approval,
protection override, merge, or change to another PR is part of this repair.
Any publication denial and the resulting commit/CI identifiers are recorded
in the coordinating handoff separately.
