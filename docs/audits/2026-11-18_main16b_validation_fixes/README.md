# Minimal fixes for main16b validation

Production fix: a928f4fad7ceb1fd0cfd3b44dc0ab38427c65385, based on
f94193009343ee767ddc96a3dacee80e659ec5a9; QIC729428582b78ab7529b3796099193649f947354a.
Latest remote main16b and the original42c4 branch both retain the failing
verification call; neither contains an equivalent fix.

Solution.lean now calls the canonical ManyBody.ChainInteraction theorem,
qualifies ManyBody.interval, and uses the existing
ManyBody.isGapped_and_groundSpace_eq_span_iff to convert the original unit-vector,
eigenvector and positive-semidefinite gap premises. No new wrapper, import,
assumption or verification proposition was introduced. Everything before the
hastings_area_law theorem is byte-identical to the base.

ViableLeadingBounds.lean only renames the unused hypothesis hh to _hh. The
hypothesis remains in the theorem; no linter is disabled.

Both modified files passed direct Lean build and strict at the exact committed
source hashes, with a single process and12GiB Lean memory limit. Both changed
proof endpoints passed axiom inspection with only propext, Classical.choice,
and Quot.sound. git diff --check passed.

The first ViableLeadingBounds attempt failed because the new TNLean namespace
prefix shadowed the underlying warm directory. Its log is preserved separately.
After copying446 exact-source dependencies and checking their artifact hashes
into the isolated overlay, its build and strict passed. No dependency was
recompiled, no old cache was mutated and no cache exporter was used.

Static reverse import closure:38 modules. Only the two modified modules were
executed at this new head. affected-status.json explicitly marks36 downstream
modules not-run, including aggregate roots; previous-base successes are not
relabeled as new-head executions. No cold/full-library build, Blueprint web/PDF,
compiled checkdecls, shared PR update or merge was performed.
