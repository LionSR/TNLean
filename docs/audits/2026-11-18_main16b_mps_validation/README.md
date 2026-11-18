# Exact main16b MPS validation

Source: f94193009343ee767ddc96a3dacee80e659ec5a9, QIC pin
729428582b78ab7529b3796099193649f947354a. No production source changed.
The old865 queue finished independently; its original source/provenance and
failures remain under evidence/pin729-mps, final455dcc64c. Those passes are not
relabeled as executions at this head.

The original77 targets, actual13 reverse-closure targets, and the previously
memory-blocked BoundaryFactorization yield82 unique targets. Target-status.json
separates build and strict pass, fail, not-run, and explicitly validated reuse.
Two prior42c4 strict successes are reused only after complete source/import and
artifact checking. All other strict passes are new exact-head executions.

BoundaryFactorization passed serial build and strict with a12288MiB Lean limit;
the original42c4 memory_exception at4096MiB is preserved in the earlier audit.
No system or security setting changed. There were no active old compilers, and
an exclusive lock was held throughout. No cache was deleted. Eligible artifacts
were copied with hash verification into /tmp/main16b-mps-olean; writable old
project caches are absent from LEAN_PATH. A1GiB disk floor and8GiB available
memory preflight guard were used. This is direct Lean compilation/strict, not
Lake build or a whole-library result.

Two defects remain at exact source:

- verification/area-law/Solution.lean:110 unknown identifier interval, and:111
  unknown identifier ChainHamiltonian. Build failed; strict was not run.
- TNLean/MPS/AreaLaw/ViableSet/ViableLeadingBounds.lean:425 unused binder hh.
  Build passed with warning; strict failed. Downstream checks continued using
  its successfully compiled artifact; the strict failure was not waived.

The thirteen affected targets have nine new build/strict passes, one failed
verification file, and three unrun aggregates. Aggregate missing-module lists
are retained; AreaLaw237, MPS753, TNLean2368 include each root itself. No cold
full closure was launched. Hastings aggregate did pass.

Nine representative area-law and MPS approximation declarations passed axiom
inspection with only propext, Classical.choice and Quot.sound. The failed
verification wrapper is not covered by this audit.

No full-library build, compiled Blueprint checkdecls, Blueprint web/PDF, shared
PR update or merge was performed. Exact-source defects and aggregate gaps must
be resolved before integration is represented as fully verified.
