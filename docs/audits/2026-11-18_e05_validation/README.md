# Final exact-snapshot validation results

Production revision: `e05d7f8907e0a4ebbcf4ad960f48958664eb7d3f`. Test revision: `207cc00e5e8e83447d0c965a12b1cc2de8f4f1e7`.
Recorded 2026-11-18T14:33:50 UTC.

The original 39 pending production modules passed Lake builds and full strict checks, including all 25 pending gap modules. RangeSquareGroundState was additionally rebuilt and strictly checked. The reverse-consumer list has 656/658 complete passes at this checkpoint; `remaining.txt` lists targets without a completed strict pass. The assigned queue has completed in the unchanged production checkout. `remaining.txt` contains the two non-passing targets; `unattempted.txt` is empty.

All three complete final regression files passed strict checks. RangeSquare took 6.01 s, Box 8.67 s, and wrappers 4.39 s. The wrapper initially lacked PinnedZeroFloorOptimizer's object file; its subsequent targeted Lake build passed in 11.70 s. The initial dependency error is retained in the log archive and is superseded by the separately recorded successful run.

`ledger.json` contains exact commands, per-file results, batch durations and disk measurements. `completed-logs.tar.gz` contains the corresponding completed build/strict logs and fixture attempts. The fixture selection record uses the unmodified selector from the exact test revision and exercises changes to each test and its owners. No production source changes, fixture repairs, full library build, CI or Blueprint builds are claimed here. Earlier worker results are not counted as new local checks.

## Strict formatting failure and isolated correction

At the production revision, `TNLean/MPS/ParentHamiltonian/LocalParentExpectationFromOpenKernel.lean:59` builds successfully but fails strict checking because one proof line exceeds 100 characters. Commit `5f9d620b4f663c8fd8695f7e1d92ae128b15c4fa` on `fix/e05-openkernel-line-wrap` only wraps that line. The complete corrected source passed strict checking in 10.89 seconds against the production dependency snapshot. The original ledger retains its failure; this separate correction is not applied to the validation checkout.

## Recovery after environment interruption

The original runner continued to 639 reverse-consumer strict passes and one recorded style failure, then stopped before the last 18 targets because free disk space fell below its 1.5 GiB guard. Recovery found no live build processes and clean worktrees at the original revisions. Only regenerable `.lake/build/ir/**/*.setup.json` metadata was removed (2062 files, 4297365380 bytes); all source, branch, object-file and evidence artifacts were preserved. The exact removal manifest is recorded. The resumed runner skips every already-recorded target, including the known failure, and validates only the final 18 targets.

## Final outcome and limits

Production remains `e05d7f8907e0a4ebbcf4ad960f48958664eb7d3f`, QIC pin `1af32a2bf77670e4fc01a7727828bcbd49d35de3`, Lean `v4.36.0-rc1`. All 39 formerly pending production targets passed build and strict; the extra RangeSquare owner also passed. Of 658 reverse consumers, 657 passed build, 656 passed strict, one failed strict formatting, and one was blocked by an actual dependency compilation error. Zero targets remain unattempted. The separate formatting correction is not counted as a pass at the original revision.

The final `TNLean.PEPS` build is blocked by `TNLean/PEPS/Examples/HoneycombCluster.lean:77:45`: unknown identifier `Edge`, followed by errors resolving `Edge.ofAdj`, `Edge.ofAdj_endpoints`, and related uses. The canonical declarations exist in `ManyBody` in the pinned `QICLean/ManyBody/Sites/Lattice/Edge.lean`; the consumer uses the unqualified names inside `TNLean.PEPS` without opening that namespace. This is a source diagnosis, not a tested repair. Secondary elaboration warnings follow the unresolved names. No proof bypasses were introduced. The independent `TNLean.PEPS.Approximation` target passed its isolated Lake build and complete strict check. The full failure log is retained.

The resumed final 18-target queue took 1809.95 seconds wall time. Its three main build batches took 330.32, 680.82 and 758.74 seconds; the last failed, and the independent approximation target passed in 6.01 seconds. Across the entire original and resumed run, recorded Lake build time totals 6429.78 seconds and strict-process time totals 4025.23 seconds (strict processes overlap, so this is not wall time). The environment interruption is not counted as build time. All three final test files from `207cc00e5e8e83447d0c965a12b1cc2de8f4f1e7` passed as separately recorded. None of these results validates a later main revision or QIC pin.

A second disk cleanup removed only 692 pre-resume generated setup metadata files, excluding paths referenced by active commands, freeing 2153002341 bytes. Both cleanup manifests are retained. At completion approximately 2.16 GiB remained free. The production worktree is clean and no builds remain running.

## Cache handoff capability

The warm local TN Lean artifact tree is retained (about 3.5 GiB), as is the pinned QIC artifact tree (about 683 MiB), with build traces and source revisions. These can be exported as a selected, manifest-bound stream without duplicating the whole cache locally. No cache archive was created or uploaded. The failed HoneycombCluster/PEPS target cannot be represented as validated. Local targeted evidence is not a successful full CI cache provenance record. Reuse under a different pin or source revision requires the existing compatibility/provenance checks; this report does not authorize cross-pin cache reuse.
