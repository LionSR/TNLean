# Final Snake local validation

Source: 42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d. QIC pin: 729428582b78ab7529b3796099193649f947354a. Compiler version, executable hash, all package revisions and source hashes are in preflight.json.

The parent explicitly authorized local recompilation after the permitted transfer route was unavailable. No exporter was retried or altered; prior transfer assessment remains in ../2026-11-18_interaction_peps_remaining/SNAKE_TRANSFER.md. Ten prerequisite compilations are explicitly recorded as cross-environment duplicate cost, not zero-duplication reuse.

Execution: python /workspace/reviews/interaction-snake-final/verify_snake.py. Compiler cwd: /workspace/tn-interaction-final. The script uses package linter/options, isolated output, an exclusive cache lock, process groups, 180-second command timeout and 1 GiB free-space guard. It performs direct Lean compilation into an overlay, not a full Lake build. No production source or existing PR was changed.

Outcome: ten prerequisite compile commands passed (36.835607 seconds), Snake compile passed (9.303505438001594 seconds), Snake strict passed (4.1810995639971225 seconds). The prerequisite modules were not separately strict-checked. No extra transitive prerequisites were compiled. The existing 107 PEPS / six owner / five fixture results retain their original execution heads and are reused only under the earlier transitive fingerprint audit.

An initial compile attempt failed before elaboration because the new overlay shadowed the existing TNLean namespace and lacked a RectangularDomain.olean link. initial-overlay-failure.jsonl preserves the exact command/exit/time; initial-overlay-failure.txt records the diagnostic. The separate final overlay was completed with 7,628 links to the existing shared cache, then the queue was restarted. No cached proof was recompiled to fix this lookup failure. Final summary.failed=0 refers only to the successful final queue, not the initial failed attempt.

Independent post-run artifact audit: python /workspace/reviews/interaction-snake-final/audit.py; 12 successful commands, 1,501 unique artifact files, zero fingerprint/hash mismatches. Full per-command fingerprints, logs, commands, UTC, PID/PGID, exits and durations are included. No compiler remains running. Free space at completion: 2,345,758,720 bytes. No full library/root/Blueprint build was attempted.
