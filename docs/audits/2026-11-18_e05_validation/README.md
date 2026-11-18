# Exact-snapshot validation checkpoint

Production revision: `e05d7f8907e0a4ebbcf4ad960f48958664eb7d3f`. Test revision: `207cc00e5e8e83447d0c965a12b1cc2de8f4f1e7`.
Recorded 2026-11-18T09:17:17 UTC.

The original 39 pending production modules passed Lake builds and full strict checks, including all 25 pending gap modules. RangeSquareGroundState was additionally rebuilt and strictly checked. The reverse-consumer list has 519/658 complete passes at this checkpoint; `remaining.txt` lists targets without a completed strict pass. Validation continues separately in the unchanged production checkout.

All three complete final regression files passed strict checks. RangeSquare took 6.01 s, Box 8.67 s, and wrappers 4.39 s. The wrapper initially lacked PinnedZeroFloorOptimizer's object file; its subsequent targeted Lake build passed in 11.70 s. The initial dependency error is retained in the log archive and is superseded by the separately recorded successful run.

`ledger.json` contains exact commands, per-file results, batch durations and disk measurements. `completed-logs.tar.gz` contains the corresponding completed build/strict logs and fixture attempts. The fixture selection record uses the unmodified selector from the exact test revision and exercises changes to each test and its owners. No production source changes, fixture repairs, full library build, CI or Blueprint builds are claimed here. Earlier worker results are not counted as new local checks.

## Strict formatting failure and isolated correction

At the production revision, `TNLean/MPS/ParentHamiltonian/LocalParentExpectationFromOpenKernel.lean:59` builds successfully but fails strict checking because one proof line exceeds 100 characters. Commit `5f9d620b4f663c8fd8695f7e1d92ae128b15c4fa` on `fix/e05-openkernel-line-wrap` only wraps that line. The complete corrected source passed strict checking in 10.89 seconds against the production dependency snapshot. The original ledger retains its failure; this separate correction is not applied to the validation checkout.
