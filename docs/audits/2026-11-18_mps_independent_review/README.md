# Independent MPS lane source review

Exact head: 550b63ccb49e4784cd42949d53996197fd0ce073
Base: b2c72008326f3166d3bcdc9e79013443142b0aa8
QIC pin: 729428582b78ab7529b3796099193649f947354a

Reviewed lane commits 54ab66ae0, 42229ed94, 550b63ccb. 85 changed production files, one unchanged allocation, one migrated fixture and three audit files. coverage.tsv records every path. declarations.json inventories 643 base / 657 head declarations; no public declaration disappears under canonical owner renaming.

Method: read the entire 4024-line token-normalized semantic diff for all85 files, then raw diff/source context for substantive changes, constructions, namespace relocation and sensitive assumptions. Normalization hides only common owner/operator/member spellings, comments and whitespace; this is not a claim to have read all8377 raw diff lines independently. Constructor/support context, scoped matrix norm introductions, model-family tuple projections, counting-helper contract and zero-gap fixture were separately inspected. No mathematical scope defect identified in these source deltas. This is static review, not Lean validation.

Shared commit81e70a7d4 is separate: stable patch ID ffd92d3018eabd9dde0ce736364cec94e6a3c614 equals b992c791dc35580cb84e1161150b98b9963284bb. Patch identity does not independently certify that shared code.

Executed actual ci_lean_checks.select with each single changed path injected in memory, reusing its actual repository import graph. Hamiltonian, OverlapEnergy, BoundaryGap and fixture changes select ground_state_gap_scope_regression; ThreeWaySplitting selects zero_gap_tn_wrappers_regression. Full results selector.json. The latter wrapper is not this lane's migrated fixture, and selection is not evidence it compiles.

Independent git diff --check passed. Exact review worktree stayed clean; remote branch rechecked at exact550 head. All87 author source hashes matched. No Lean build/strict or full integrated source-sync run: isolated checkout lacks matching dependency products and PEPS/shared consumer integration remains external. Therefore elaboration, complete dependency closure and all new-pin compilation remain blocking validation gates; no ready-to-merge conclusion.

## Publication accounting

The 92 coverage rows are 85 changed production + 1 unchanged allocated production + 1 migrated fixture + 3 lane audit files + 2 separately accounted shared files. Publication rechecked all 86 declaration-inventory source hashes against exact head and the 85-file production commit manifest; all five recorded selector cases passed. See publication-checks.json. This publication performs no new Lean compilation or integrated source-sync. The source snapshots under the local base/ directory are recoverable from the exact base commit and are not duplicated here. The local report-generation helper is not validation evidence and is not included.
